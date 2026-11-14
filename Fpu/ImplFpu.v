(*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(*
 * Pipelined FPU (`ImplFpu.v`).
 *
 * State (`implTree ls`): the architectural state `fpuArchTree` of `FpuArch.v`, a control block
 * `ctl` = { `pend` : one bit per f register with an FP operation in flight, `lpend` : one bit
 * per f register reserved by a load, `intBusy` : an integer-result operation is in flight },
 * and the execution fus `ls` (`FpuFU.v`).
 *
 * Scoreboard: an f register is busy if its `pend` or `lpend` bit is set.  Only RAW and WAW are
 * blocked (sources and destination must not be busy); there is no WAR stall, since operands
 * are read at issue.  Results are written back out of order, as soon as a fu produces them.
 *
 * Interface (every call has a ready flag; a call that is not ready changes nothing):
 * - `fpuIssue pkt x` : Bool -- issue one decoded instruction to the first fu that accepts
 *   it.  Ready iff rs1, rs2, rs3 are not busy, and rd is not busy (f result) or no integer
 *   operation is in flight (integer result), and that fu can accept.  Sets `fs` to Dirty.
 * - `fpuIntResp` : Option (Bit xlen) -- the result of the integer-result operation, once done.
 * - `fpuReserve rd` : Bool / `fpuFill rd v` : Bool -- an FP load: reserve the destination at
 *   issue (sets `fs` to Dirty), write the loaded value later.
 * - `fpuReadT idx` : Option (Bit flen) / `fpuWriteT idx v` : Bool -- raw access (moves, stores);
 *   ready iff `idx` is not busy.
 * - `frmRead`, `frmWrite`, `fsRead`, `fsWrite` -- always ready.
 * - `fflagsReadT`, `fcsrReadT`, `fflagsWriteT`, `fcsrWriteT` -- ready iff no FP operation is in
 *   flight (`pend = 0` and not `intBusy`).
 * Internal rules: each fu's own rules, and one write-back rule per fu (f results).
 *
 * `fpuImplMod` adds driver rules calling every interface action with arbitrary arguments; it is
 * the standalone module refined against `SpecFpu.fpuSpecMod` (`Proof/FpuRefinement.v`).
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations Composition.
From Fpu Require Import FpUtil FpCore FpuArch SpecFpu FpuFU.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ---------------------------------------------------------------------------
 * One-bit-per-register vectors
 * --------------------------------------------------------------------------- *)

Definition RegVecSz : Z := 32.

Section BitVec.
  Variable ty : Kind -> Type.

  Definition bitMaskE (i : Expr ty (Bit FprIdxSz)) : Expr ty (Bit RegVecSz) := Sll (cst RegVecSz 1) i.
  Definition bitTestE (w : Expr ty (Bit RegVecSz)) (i : Expr ty (Bit FprIdxSz)) : Expr ty Bool :=
    Not (Eq (And [ w ; bitMaskE i ]) (cst RegVecSz 0)).
  Definition bitSetE (w : Expr ty (Bit RegVecSz)) (i : Expr ty (Bit FprIdxSz)) : Expr ty (Bit RegVecSz) :=
    Or [ w ; bitMaskE i ].
  Definition bitClrE (w : Expr ty (Bit RegVecSz)) (i : Expr ty (Bit FprIdxSz)) : Expr ty (Bit RegVecSz) :=
    And [ w ; Not (bitMaskE i) ].
End BitVec.

(* Bit `r` of `w`. *)
Definition bitOf (w : bits RegVecSz) (r : bits FprIdxSz) : bool := Z.testbit (Zmod.unsigned w) (Zmod.unsigned r).

(* ---------------------------------------------------------------------------
 * Control block
 * --------------------------------------------------------------------------- *)

Definition ctlTree : Tree Elem :=
  Node "ctl" [
    Leaf "pend"    (EReg (Build_Reg (Bit RegVecSz) (Some (getDefault _)))) ;
    Leaf "lpend"   (EReg (Build_Reg (Bit RegVecSz) (Some (getDefault _)))) ;
    Leaf "intBusy" (EReg (Build_Reg Bool (Some (getDefault _))))
  ].

Section Ctl.
  Variable ty : Kind -> Type.
  Definition ctlReadPend : Action ty ctlTree (Bit RegVecSz) := RegRead v <- "ctl.pend" in ctlTree ; Return (#v).
  Definition ctlWritePend (v : Expr ty (Bit RegVecSz)) : Action ty ctlTree (Bit 0) := RegWrite "ctl.pend" in ctlTree <- v ; Retv.
  Definition ctlReadLpend : Action ty ctlTree (Bit RegVecSz) := RegRead v <- "ctl.lpend" in ctlTree ; Return (#v).
  Definition ctlWriteLpend (v : Expr ty (Bit RegVecSz)) : Action ty ctlTree (Bit 0) := RegWrite "ctl.lpend" in ctlTree <- v ; Retv.
  Definition ctlReadIntBusy : Action ty ctlTree Bool := RegRead v <- "ctl.intBusy" in ctlTree ; Return (#v).
  Definition ctlWriteIntBusy (v : Expr ty Bool) : Action ty ctlTree (Bit 0) := RegWrite "ctl.intBusy" in ctlTree <- v ; Retv.
End Ctl.

Section ImplFpu.
  Variable F : FpFmt.
  Variable xlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.

  Local Abbreviation FU := (FU F xlen narrow).
  Local Abbreviation FUInK := (FUInK F xlen narrow).
  Local Abbreviation PktK := (FpuPktK narrow).
  Local Abbreviation FUOutK := (FUOutK F xlen).
  Local Abbreviation ResK := (FpuResK F xlen).

  Fixpoint fusTree (ls : list FU) : Tree Elem :=
    match ls with
    | nil => Node "fus" []
    | L :: rest => Node "fus" [ fuTree _ _ _ L ; fusTree rest ]
    end.

  Definition implTree (ls : list FU) : Tree Elem :=
    Node "fpu" [ fpuArchTree flen ; ctlTree ; fusTree ls ].

  (* --- FU-list actions --- *)
  Section FUActions.
    Variable ty : Kind -> Type.

    (* Enqueue `inp` into the first fu accepting `pkt`, if `go` and that fu can accept.
     * Returns whether it was enqueued. *)
    Fixpoint tryEnqFUs (ls : list FU) (go : ty Bool) (pkt : ty PktK) (inp : ty FUInK)
      : Action ty (fusTree ls) Bool :=
      match ls return Action ty (fusTree ls) Bool with
      | nil => Return (Const ty Bool false)
      | L :: rest =>
          LetIf r : Bool <- If (fuAccepts _ _ _ L ty pkt) Then (
            LetA ce : Bool <- liftAction child0Path (fuCanEnq _ _ _ L ty) ;
            Let ok : Bool <- And [ #go ; #ce ] ;
            If #ok Then (liftAction child0Path (fuEnq _ _ _ L ty inp)) Else Retv ;
            Return #ok
          ) Else (
            liftAction child1Path (tryEnqFUs rest go pkt inp)
          ) ;
          Return #r
      end.

    (* Dequeue the first fu whose head is a finished integer-result operation. *)
    Fixpoint intRespFUs (ls : list FU) : Action ty (fusTree ls) (Option ResK) :=
      match ls return Action ty (fusTree ls) (Option ResK) with
      | nil => Return (mkNone ty)
      | L :: rest =>
          LetA o : Option FUOutK <- liftAction child0Path (fuFirst _ _ _ L ty) ;
          LetIf r : Option ResK <- If (And [ #o`"valid" ; Not (#o`"data"`"res"`"writesF") ]) Then (
            Act (liftAction child0Path (fuDeq _ _ _ L ty)) ;
            Return (mkSome (#o`"data"`"res"))
          ) Else (
            liftAction child1Path (intRespFUs rest)
          ) ;
          Return #r
      end.

    (* Rules of every fu, given how to lift a fu action to the top tree and the write-back
     * rule of a fu. *)
    Fixpoint fusRules (Ttop : Tree Elem)
      (wb : forall L : FU, (forall k, Action ty (fuTree _ _ _ L) k -> Action ty Ttop k) -> Action ty Ttop (Bit 0))
      (ls : list FU) : (forall k, Action ty (fusTree ls) k -> Action ty Ttop k) -> list (Action ty Ttop (Bit 0)) :=
      match ls return (forall k, Action ty (fusTree ls) k -> Action ty Ttop k) -> list (Action ty Ttop (Bit 0)) with
      | nil => fun _ => []
      | L :: rest => fun lf =>
          wb L (fun k a => lf k (liftAction child0Path a))
          :: map (fun r => lf _ (liftAction child0Path r)) (fuRules _ _ _ L ty)
          ++ fusRules Ttop wb rest (fun k a => lf k (liftAction child1Path a))
      end.
  End FUActions.

  Variable ls : list FU.
  Local Abbreviation IT := (implTree ls).

  Section Actions.
    Variable ty : Kind -> Type.

    Definition liftArch {k} (a : Action ty (fpuArchTree flen) k) : Action ty IT k := liftAction child0Path a.
    Definition liftCtl {k} (a : Action ty ctlTree k) : Action ty IT k := liftAction child1Path a.
    Definition liftFUs {k} (a : Action ty (fusTree ls) k) : Action ty IT k := liftAction child2Path a.

    Definition busyE (pend lpend : ty (Bit RegVecSz)) (r : Expr ty (Bit FprIdxSz)) : Expr ty Bool :=
      Or [ bitTestE ty (#pend) r ; bitTestE ty (#lpend) r ].

    (* The scoreboard allows issuing `pkt` (`wf`: it writes an f register). *)
    Definition sbOkE (pend lpend : ty (Bit RegVecSz)) (ib : ty Bool) (pkt : ty PktK) (wf : ty Bool) : Expr ty Bool :=
      And [ Not (busyE pend lpend (##pkt`"rs1")) ;
            Not (busyE pend lpend (##pkt`"rs2")) ;
            Not (busyE pend lpend (##pkt`"rs3")) ;
            ITE (#wf) (Not (busyE pend lpend (##pkt`"rd"))) (Not (#ib)) ].

    Definition fpuIssue (pkt : ty PktK) (x : ty (Bit xlen)) : Action ty IT Bool :=
      LetA pend  : Bit RegVecSz <- liftCtl (ctlReadPend ty) ;
      LetA lpend : Bit RegVecSz <- liftCtl (ctlReadLpend ty) ;
      LetA ib    : Bool         <- liftCtl (ctlReadIntBusy ty) ;
      LetA frm   : Bit 3        <- liftArch (archReadFrm flen ty) ;
      LetA a     : Bit flen     <- liftArch (archReadFpr flen ty (##pkt`"rs1")) ;
      LetA b     : Bit flen     <- liftArch (archReadFpr flen ty (##pkt`"rs2")) ;
      LetA c     : Bit flen     <- liftArch (archReadFpr flen ty (##pkt`"rs3")) ;
      Let op     : FpuOpK narrow <- ##pkt`"op" ;
      Let wf     : Bool         <- Not (opWritesXE narrow ty op) ;
      Let sbOk   : Bool         <- sbOkE pend lpend ib pkt wf ;
      Let inp    : FUInK      <- STRUCT { "pkt" ::= #pkt ; "rm" ::= resolveRm ty (##pkt`"rm") (#frm) ;
                                            "a" ::= #a ; "b" ::= #b ; "c" ::= #c ; "x" ::= #x } ;
      LetA ok    : Bool         <- liftFUs (tryEnqFUs ty ls sbOk pkt inp) ;
      If #ok Then (
        If #wf Then (liftCtl (ctlWritePend ty (bitSetE ty (#pend) (##pkt`"rd")))) Else (liftCtl (ctlWriteIntBusy ty (Const ty Bool true))) ;
        liftArch (archWriteFs flen ty (cst 2 FsDirty))
      ) Else Retv ;
      Return #ok.

    Definition fpuIntResp : Action ty IT (Option (Bit xlen)) :=
      LetA r : Option ResK <- liftFUs (intRespFUs ty ls) ;
      If (#r`"valid") Then (
        LetA ff : Bit 5 <- liftArch (archReadFflags flen ty) ;
        Act (liftArch (archWriteFflags flen ty (Or [ #ff ; #r`"data"`"flags" ]))) ;
        liftCtl (ctlWriteIntBusy ty (Const ty Bool false))
      ) Else Retv ;
      Return (STRUCT { "data" ::= #r`"data"`"xres" ; "valid" ::= #r`"valid" } : Expr ty (Option (Bit xlen))).

    Definition fpuReserve (rd : ty (Bit FprIdxSz)) : Action ty IT Bool :=
      LetA pend  : Bit RegVecSz <- liftCtl (ctlReadPend ty) ;
      LetA lpend : Bit RegVecSz <- liftCtl (ctlReadLpend ty) ;
      Let ok : Bool <- Not (busyE pend lpend (#rd)) ;
      If #ok Then (
        Act (liftCtl (ctlWriteLpend ty (bitSetE ty (#lpend) (#rd)))) ;
        liftArch (archWriteFs flen ty (cst 2 FsDirty))
      ) Else Retv ;
      Return #ok.

    Definition fpuFill (rd : ty (Bit FprIdxSz)) (v : ty (Bit flen)) : Action ty IT Bool :=
      LetA lpend : Bit RegVecSz <- liftCtl (ctlReadLpend ty) ;
      Let ok : Bool <- bitTestE ty (#lpend) (#rd) ;
      If #ok Then (
        Act (liftArch (archWriteFpr flen ty (#rd) (#v))) ;
        liftCtl (ctlWriteLpend ty (bitClrE ty (#lpend) (#rd)))
      ) Else Retv ;
      Return #ok.

    Definition fpuReadT (idx : ty (Bit FprIdxSz)) : Action ty IT (Option (Bit flen)) :=
      LetA pend  : Bit RegVecSz <- liftCtl (ctlReadPend ty) ;
      LetA lpend : Bit RegVecSz <- liftCtl (ctlReadLpend ty) ;
      LetA v     : Bit flen     <- liftArch (fpuRead F ty (#idx)) ;
      Return (STRUCT { "data" ::= #v ; "valid" ::= Not (busyE pend lpend (#idx)) } : Expr ty (Option (Bit flen))).

    Definition fpuWriteT (idx : ty (Bit FprIdxSz)) (v : ty (Bit flen)) : Action ty IT Bool :=
      LetA pend  : Bit RegVecSz <- liftCtl (ctlReadPend ty) ;
      LetA lpend : Bit RegVecSz <- liftCtl (ctlReadLpend ty) ;
      Let ok : Bool <- Not (busyE pend lpend (#idx)) ;
      If #ok Then (liftArch (fpuWrite F ty (#idx) (#v))) Else Retv ;
      Return #ok.

    (* No FP operation in flight. *)
    Definition drainedE (pend : ty (Bit RegVecSz)) (ib : ty Bool) : Expr ty Bool :=
      And [ Eq (#pend) (cst RegVecSz 0) ; Not (#ib) ].

    Definition fpuDrained : Action ty IT Bool :=
      LetA pend : Bit RegVecSz <- liftCtl (ctlReadPend ty) ;
      LetA ib   : Bool         <- liftCtl (ctlReadIntBusy ty) ;
      Return (drainedE pend ib).

    Definition fpuFflagsReadT : Action ty IT (Option (Bit 5)) :=
      LetA ok : Bool  <- fpuDrained ;
      LetA v  : Bit 5 <- liftArch (fflagsRead F ty) ;
      Return (STRUCT { "data" ::= #v ; "valid" ::= #ok } : Expr ty (Option (Bit 5))).

    Definition fpuFcsrReadT : Action ty IT (Option (Bit 8)) :=
      LetA ok : Bool  <- fpuDrained ;
      LetA v  : Bit 8 <- liftArch (fcsrRead F ty) ;
      Return (STRUCT { "data" ::= #v ; "valid" ::= #ok } : Expr ty (Option (Bit 8))).

    Definition fpuFflagsWriteT (v : ty (Bit 5)) : Action ty IT Bool :=
      LetA ok : Bool <- fpuDrained ;
      If #ok Then (liftArch (fflagsWrite F ty (#v))) Else Retv ;
      Return #ok.

    Definition fpuFcsrWriteT (v : ty (Bit 8)) : Action ty IT Bool :=
      LetA ok : Bool <- fpuDrained ;
      If #ok Then (liftArch (fcsrWrite F ty (#v))) Else Retv ;
      Return #ok.

    Definition fpuFrmRead : Action ty IT (Bit 3) := liftArch (frmRead F ty).
    Definition fpuFrmWrite (v : ty (Bit 3)) : Action ty IT (Bit 0) := liftArch (frmWrite F ty (#v)).
    Definition fpuFsRead : Action ty IT (Bit 2) := liftArch (fsRead F ty).
    Definition fpuFsWrite (v : ty (Bit 2)) : Action ty IT (Bit 0) := liftArch (fsWrite F ty (#v)).

    (* Write-back of a finished f result from a fu. *)
    Definition wbRule (L : FU) (lf : forall k, Action ty (fuTree _ _ _ L) k -> Action ty IT k)
      : Action ty IT (Bit 0) :=
      LetA o : Option FUOutK <- lf _ (fuFirst _ _ _ L ty) ;
      If (And [ #o`"valid" ; #o`"data"`"res"`"writesF" ]) Then (
        Act (liftArch (archWriteFpr flen ty (#o`"data"`"rd") (#o`"data"`"res"`"res"))) ;
        LetA ff   : Bit 5        <- liftArch (archReadFflags flen ty) ;
        Act (liftArch (archWriteFflags flen ty (Or [ #ff ; #o`"data"`"res"`"flags" ]))) ;
        LetA pend : Bit RegVecSz <- liftCtl (ctlReadPend ty) ;
        Act (liftCtl (ctlWritePend ty (bitClrE ty (#pend) (#o`"data"`"rd")))) ;
        lf _ (fuDeq _ _ _ L ty)
      ) Else Retv ;
      Retv.

    Definition fpuImplRules : list (Action ty IT (Bit 0)) :=
      fusRules ty IT wbRule ls (fun k a => liftFUs a).

    (* Standalone harness: every interface call with arbitrary arguments. *)
    Definition fpuDriverRules : list (Action ty IT (Bit 0)) := [
      ( Random pkt : PktK ; Random x : Bit xlen ; Act (fpuIssue pkt x) ; Retv ) ;
      ( Act fpuIntResp ; Retv ) ;
      ( Random rd : Bit FprIdxSz ; Act (fpuReserve rd) ; Retv ) ;
      ( Random rd : Bit FprIdxSz ; Random v : Bit flen ; Act (fpuFill rd v) ; Retv ) ;
      ( Random i : Bit FprIdxSz ; Random v : Bit flen ; Act (fpuWriteT i v) ; Retv ) ;
      ( Random v : Bit 3 ; fpuFrmWrite v ) ;
      ( Random v : Bit 5 ; Act (fpuFflagsWriteT v) ; Retv ) ;
      ( Random v : Bit 8 ; Act (fpuFcsrWriteT v) ; Retv ) ;
      ( Random v : Bit 2 ; fpuFsWrite v ) ].
  End Actions.

  Definition fpuImplMod : Mod IT := fun ty => (fpuImplRules ty ++ fpuDriverRules ty)%list.
End ImplFpu.
