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
 * Functional units of the FPU (`FpuFU.v`).
 *
 * An FU is an in-order execution unit with a uniform interface (record `FU`):
 * - input `FUInK`: the decoded packet, the resolved rounding mode, the three raw operand
 *   registers and the integer operand -- everything `SpecFpu.execResOf` needs;
 * - output `FUOutK`: the destination register and the result (`FpuResK`);
 * - `fuAccepts pkt`: which packets the FU executes (used for routing at issue);
 * - `fuCanEnq` / `fuEnq` / `fuFirst` / `fuDeq` and internal rules `fuRules`.
 *
 * FUs built here, for the FPU's own format `F` (all execute exactly the spec's algorithm):
 * - `pipeFU`: `stagedPipe` running the pipe unit of `ImplFpuUnits.v` (every op except DIV,
 *   SQRT and the narrow conversions);
 * - `divFU`, `sqrtFU`: `stagedIter` running the divide / square-root units;
 * - `cvtFU`: the narrow conversions (`cvtN` family; only if `narrow` is not empty),
 *   computed at enqueue into a 1-entry output FIFO.
 * Each unit is wrapped with the metadata `{rd, wf}` (destination, "writes an f register"), which
 * travels with the operation (`withMeta*`).
 *
 * `fpuFUs` is the standard FU list.  See `Proof/FpuFUProof.v` for the FU correctness theorems.
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations Composition.
From Fpu Require Import FpUtil FpCore IntMul ImplStaged ImplFpuUnits FpuArch SpecFpu.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Definition FUMetaK : Kind :=
  STRUCT_TYPE {
    "rd" :: Bit FprIdxSz ;
    "wf" :: Bool
  }.

(* A unit state with its metadata. *)
Definition WithMetaK (SK : Kind) : Kind :=
  STRUCT_TYPE {
    "meta" :: FUMetaK ;
    "st"   :: SK
  }.

Section FUs.
  Variable F : FpFmt.
  Variable xlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.

  Local Abbreviation PktK := (FpuPktK narrow).
  Local Abbreviation e := (fmtE F).
  Local Abbreviation f := (fmtF F).

  Definition FUInK : Kind :=
    STRUCT_TYPE {
      "pkt" :: PktK ;
      "rm"  :: Bit 3 ;
      "a"   :: Bit flen ;
      "b"   :: Bit flen ;
      "c"   :: Bit flen ;
      "x"   :: Bit xlen
    }.

  Definition FUOutK : Kind :=
    STRUCT_TYPE {
      "rd"  :: Bit FprIdxSz ;
      "res" :: FpuResK F xlen
    }.

  Record FU := mkFU {
    fuTree    : Tree Elem ;
    fuAccepts : forall ty, ty PktK -> Expr ty Bool ;
    fuCanEnq  : forall ty, Action ty fuTree Bool ;
    fuEnq     : forall ty, ty FUInK -> Action ty fuTree (Bit 0) ;
    fuFirst   : forall ty, Action ty fuTree (Option FUOutK) ;
    fuDeq     : forall ty, Action ty fuTree (Bit 0) ;
    fuRules   : forall ty, list (Action ty fuTree (Bit 0))
  }.

  Section Exprs.
    Variable ty : Kind -> Type.

    (* Operation family tests (routing). *)
    Definition isDivP  (pkt : ty PktK) : Expr ty Bool := (##pkt`"op") `? "div".
    Definition isSqrtP (pkt : ty PktK) : Expr ty Bool := (##pkt`"op") `? "sqrt".
    Definition isCvtNP (pkt : ty PktK) : Expr ty Bool := (##pkt`"op") `? "cvtN".

    (* The narrow-conversion options of a packet. *)
    Definition cvtNOf (pkt : ty PktK) : Expr ty (CvtNOptK narrow) := (##pkt`"op") `! "cvtN".

    (* `nidx` names an entry of `narrow`. *)
    Definition nidxOk (pkt : ty PktK) : Expr ty Bool :=
      Or (map (fun k => Eq ((cvtNOf pkt) `"nidx") (cst (NIdxSz narrow) (Z.of_nat k))) (seq 0 (length narrow))).

    Definition fuMetaOf (inp : ty FUInK) : LetExpr ty FUMetaK :=
      LetE op : FpuOpK narrow <- ##inp`"pkt"`"op" ;
      RetE (STRUCT { "rd" ::= ##inp`"pkt"`"rd" ; "wf" ::= Not (opWritesXE narrow ty op) } : Expr ty FUMetaK).

    (* The request of an input to a unit. *)
    Definition reqOf (inp : ty FUInK) : LetExpr ty (FpReqK e f xlen) :=
      LetE pkt : PktK          <- ##inp`"pkt" ;
      LetE op  : FpuOpK narrow <- ##pkt`"op" ;
      LETE od  : FpOpDK        <- decodeOp narrow ty op ;
      LetE a   : Bit flen      <- ##inp`"a" ;
      LetE b   : Bit flen      <- ##inp`"b" ;
      LetE c   : Bit flen      <- ##inp`"c" ;
      RetE (STRUCT { "op" ::= #od ; "rm" ::= ##inp`"rm" ; "a" ::= #a ; "b" ::= #b ;
                     "c" ::= #c ; "x" ::= ##inp`"x" } : Expr ty (FpReqK e f xlen)).
  End Exprs.

  (* ---------------------------------------------------------------------------
   * Wrapping a staged unit with metadata
   * --------------------------------------------------------------------------- *)
  Section WithMeta.
    Variable SK OK : Kind.
    Variable initU   : forall ty, ty (FpReqK e f xlen) -> LetExpr ty SK.
    Variable stepU   : forall ty, ty SK -> LetExpr ty SK.
    Variable finishU : forall ty, ty SK -> LetExpr ty OK.
    (* How a unit output becomes a result (without `writesF`). *)
    Variable resU    : forall ty, ty OK -> Expr ty (FpResK e f xlen).

    Definition withMetaInit (ty : Kind -> Type) (inp : ty FUInK) : LetExpr ty (WithMetaK SK) :=
      LETE meta : FUMetaK      <- fuMetaOf ty inp ;
      LETE req : FpReqK e f xlen <- reqOf ty inp ;
      LETE st0 : SK              <- initU ty req ;
      RetE (STRUCT { "meta" ::= #meta ; "st" ::= #st0 } : Expr ty (WithMetaK SK)).

    Definition withMetaStep (ty : Kind -> Type) (s : ty (WithMetaK SK)) : LetExpr ty (WithMetaK SK) :=
      LetE cur : SK <- ##s`"st" ;
      LETE nxt : SK <- stepU ty cur ;
      RetE (STRUCT { "meta" ::= ##s`"meta" ; "st" ::= #nxt } : Expr ty (WithMetaK SK)).

    Definition withMetaFinish (ty : Kind -> Type) (s : ty (WithMetaK SK)) : LetExpr ty FUOutK :=
      LetE cur : SK               <- ##s`"st" ;
      LETE o   : OK               <- finishU ty cur ;
      LetE r   : FpResK e f xlen  <- resU ty o ;
      RetE (STRUCT {
        "rd"  ::= ##s`"meta"`"rd" ;
        "res" ::= STRUCT {
          "res"     ::= ##r`"res" ;
          "xres"    ::= ##r`"xres" ;
          "flags"   ::= ##r`"flags" ;
          "writesF" ::= ##s`"meta"`"wf" } } : Expr ty FUOutK).
  End WithMeta.

  (* ---------------------------------------------------------------------------
   * The fus
   * --------------------------------------------------------------------------- *)

  Definition resId (ty : Kind -> Type) (o : ty (FpResK e f xlen)) : Expr ty (FpResK e f xlen) := #o.
  Definition resOut (ty : Kind -> Type) (o : ty (FpOutK e f)) : Expr ty (FpResK e f xlen) := fpRes e f xlen ty o.

  Section PipeFU.
    Variable mul_stages mul_bps : nat.
    Local Abbreviation SK := (PipeStateK e f xlen (mul_stages * mul_bps)).

    Definition plInit := withMetaInit SK (pipeInit e f xlen mul_stages mul_bps).
    Definition plStep := withMetaStep SK (pipeStep e f xlen mul_stages mul_bps).
    Definition plFinish := withMetaFinish SK (FpResK e f xlen) (pipeFinish e f xlen mul_stages mul_bps) resId.

    Definition pipeFU : FU := {|
      fuTree    := stagedPipeTree (WithMetaK SK) mul_stages ;
      fuAccepts := fun ty pkt =>
        And [ Not (isDivP ty pkt) ; Not (isSqrtP ty pkt) ; Not (isCvtNP ty pkt) ] ;
      fuCanEnq  := fun ty => stagedPipeCanEnq (WithMetaK SK) mul_stages ty ;
      fuEnq     := fun ty inp => @stagedPipeEnq FUInK (WithMetaK SK) mul_stages plInit ty inp ;
      fuFirst   := fun ty => stagedPipeFirst (WithMetaK SK) FUOutK mul_stages plFinish ty ;
      fuDeq     := fun ty => stagedPipeDeq (WithMetaK SK) mul_stages ty ;
      fuRules   := fun ty => stagedPipeAllStageRules (WithMetaK SK) mul_stages plStep ty
    |}.
  End PipeFU.

  Section DivFU.
    Local Abbreviation SK := (DivStateK e f).
    Local Abbreviation n := (divSteps f).

    Definition dlSteps (ty : Kind -> Type) (_ : ty FUInK) : LetExpr ty (Bit (iterStepsSz n)) :=
      RetE (Const ty (Bit (iterStepsSz n)) (bits.of_Z (iterStepsSz n) (Z.of_nat n))).
    Definition dlInit := withMetaInit SK (divInit e f xlen).
    Definition dlStep := withMetaStep SK (divStep e f).
    Definition dlFinish := withMetaFinish SK (FpOutK e f) (divFinish e f) resOut.

    Definition divFU : FU := {|
      fuTree    := stagedIterTree (WithMetaK SK) n ;
      fuAccepts := fun ty pkt => isDivP ty pkt ;
      fuCanEnq  := fun ty => stagedIterCanEnq (WithMetaK SK) n ty ;
      fuEnq     := fun ty inp => @stagedIterEnq FUInK (WithMetaK SK) n dlSteps dlInit ty inp ;
      fuFirst   := fun ty => stagedIterFirst (WithMetaK SK) FUOutK n dlFinish ty ;
      fuDeq     := fun ty => stagedIterDeq (WithMetaK SK) n ty ;
      fuRules   := fun ty => [ stagedIterStep (WithMetaK SK) n dlStep ty ]
    |}.
  End DivFU.

  Section SqrtFU.
    Local Abbreviation SK := (SqrtStateK e f).
    Local Abbreviation n := (sqrtSteps f).

    Definition slSteps (ty : Kind -> Type) (_ : ty FUInK) : LetExpr ty (Bit (iterStepsSz n)) :=
      RetE (Const ty (Bit (iterStepsSz n)) (bits.of_Z (iterStepsSz n) (Z.of_nat n))).
    Definition slInit := withMetaInit SK (sqrtInit true e f xlen).
    Definition slStep := withMetaStep SK (sqrtStep e f).
    Definition slFinish := withMetaFinish SK (FpOutK e f) (sqrtFinish true e f) resOut.

    Definition sqrtFU : FU := {|
      fuTree    := stagedIterTree (WithMetaK SK) n ;
      fuAccepts := fun ty pkt => isSqrtP ty pkt ;
      fuCanEnq  := fun ty => stagedIterCanEnq (WithMetaK SK) n ty ;
      fuEnq     := fun ty inp => @stagedIterEnq FUInK (WithMetaK SK) n slSteps slInit ty inp ;
      fuFirst   := fun ty => stagedIterFirst (WithMetaK SK) FUOutK n slFinish ty ;
      fuDeq     := fun ty => stagedIterDeq (WithMetaK SK) n ty ;
      fuRules   := fun ty => [ stagedIterStep (WithMetaK SK) n slStep ty ]
    |}.
  End SqrtFU.

  Section CvtFU.
    Variable ty : Kind -> Type.

    Definition cvtOut (inp : ty FUInK) : LetExpr ty FUOutK :=
      LetE pkt  : PktK                <- ##inp`"pkt" ;
      LetE op   : FpuOpK narrow       <- ##pkt`"op" ;
      LetE pN   : CvtNOptK narrow     <- #op `! "cvtN" ;
      LetE toN  : Bool                <- ##pN`"toNarrow" ;
      LetE nidx : Bit (NIdxSz narrow) <- ##pN`"nidx" ;
      LetE rm   : Bit 3               <- ##inp`"rm" ;
      LetE a    : Bit flen            <- ##inp`"a" ;
      LetE r0   : FpuResK F xlen   <- FpuRes0 F xlen ty ;
      LETE r    : FpuResK F xlen   <- narrowSel true F xlen narrow ty toN rm a nidx narrow 0 r0 ;
      RetE (STRUCT { "rd" ::= ##pkt`"rd" ; "res" ::= #r } : Expr ty FUOutK).
  End CvtFU.

  Definition cvtFU : FU := {|
    fuTree    := fifoTree 1 FUOutK ;
    fuAccepts := fun ty pkt => And [ isCvtNP ty pkt ; nidxOk ty pkt ] ;
    fuCanEnq  := fun ty => (LetA full : Bool <- @isFull 1 FUOutK ty ; Return (Not #full)) ;
    fuEnq     := fun ty inp => (LetL o : FUOutK <- cvtOut ty inp ; @enq 1 FUOutK ty o) ;
    fuFirst   := fun ty => @first 1 FUOutK ty ;
    fuDeq     := fun ty => @deq 1 FUOutK ty ;
    fuRules   := fun ty => []
  |}.

  (* The standard FUs: pipe (multiplier with `mul_stages` stages of `mul_bps` bits), divide,
   * square root, and the narrow-conversion FU if there are narrow formats. *)
  Definition fpuFUs (mul_stages mul_bps : nat) : list FU :=
    [ pipeFU mul_stages mul_bps ; divFU ; sqrtFU ] ++ (match narrow with nil => [] | _ => [ cvtFU ] end).
End FUs.
