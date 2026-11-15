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
 * Register-level FPU spec (`SpecFpu.v`): the atomic FPU.
 *
 * Parameters: the FPU's own format `F` (`fmtE`, `fmtF` = exponent and fraction widths), `xlen`,
 * and a static list `narrow` of boxed narrow formats.  The FP registers are `fmtW F` bits wide
 * (`flen` below abbreviates it).  The FPU is format-ignorant: packets carry no format.  The
 * operation is a tagged union of families with their options (`FpuOpK`, decoded once by
 * `decodeOp` into the core's flat record).  Narrow formats only appear in the `cvtN` family,
 * whose payload `{toNarrow; nidx}` selects the direction and the narrow format (`nidx`,
 * `log2_up (length narrow)` bits, indexes `narrow`); narrow values live NaN-boxed in the
 * registers (as Zfhmin / Zfbfmin require).  Zfa FLI is not an operation: write `fliConst idx`
 * with `fpuWrite`.
 *
 * State: the architectural FP state `fpuArchTree` of `FpuArch.v` (registers `fpr_0 .. fpr_1f`,
 * `frm`, `fflags`, `fs`).
 *
 * Actions (all atomic; the impl offers the same calls with ready flags, see `ImplFpu.v`):
 * - `fpuExec pkt xval`: one decoded FP instruction (`FpuPktK narrow`: op, rm, register
 *   indices), with `xval` = the integer operand.  Reads its sources, resolves the rounding mode
 *   (DYN -> `frm`), computes, writes `fpr[rd]` unless the result goes to an integer register,
 *   ORs the flags into `fflags`, sets `fs` to Dirty, and returns the integer result.
 * - `fpuRead idx` / `fpuWrite idx v`: raw access to `fpr[idx]` for moves, loads and stores (no
 *   NaN-box check on read; `fpuWrite` sets `fs` to Dirty).  Box narrow loads with `boxTo`.
 * - `fcsrRead` / `fcsrWrite`, `frmRead` / `frmWrite`, `fflagsRead` / `fflagsWrite`,
 *   `fsRead` / `fsWrite`.  Writes of `fcsr` / `frm` / `fflags` set `fs` to Dirty.
 *
 * Section `Semantics` gives each action as a Gallina function on the state (`execSem`,
 * `writeSem`, ...), for replay by a parent proof; `Proof/SpecFpuLemmas.v` proves that the actions
 * compute them.
 *
 * Illegal-instruction checks (FS = Off, reserved rounding modes, unsupported ops) are the
 * main pipeline's job.
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations Composition Semantics.
From Fpu Require Import FpUtil FpCore FpuArch.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Record FpFmt := mkFpFmt { fmtE : Z ; fmtF : Z }.

Definition fmtW (F : FpFmt) : Z := fmtF F + fmtE F + 1.

Definition FmtS : FpFmt := mkFpFmt 8 23.     (* binary32 *)
Definition FmtD : FpFmt := mkFpFmt 11 52.    (* binary64 *)
Definition FmtH : FpFmt := mkFpFmt 5 10.     (* binary16 (FP16) *)
Definition FmtQ : FpFmt := mkFpFmt 15 112.   (* binary128 *)
Definition FmtB : FpFmt := mkFpFmt 8 7.      (* bfloat16 *)

Definition FsOff     : Z := 0.
Definition FsInitial : Z := 1.
Definition FsClean   : Z := 2.
Definition FsDirty   : Z := 3.

(* Width of the narrow-format index. *)
Definition NIdxSz (narrow : list FpFmt) : Z := Z.log2_up (Z.of_nat (length narrow)).

(* Options of the operation families (payloads of the operation union). *)
Definition AddOptK    : Kind := STRUCT_TYPE { "negB" :: Bool }.
Definition FmaOptK    : Kind := STRUCT_TYPE { "negProd" :: Bool ; "negAdd" :: Bool }.
Definition MinMaxOptK : Kind := STRUCT_TYPE { "isMax" :: Bool ; "nanProp" :: Bool }.
Definition SgnjOptK   : Kind := STRUCT_TYPE { "mode" :: Bit 2 }.
Definition CmpOptK    : Kind := STRUCT_TYPE { "mode" :: Bit 2 ; "quiet" :: Bool }.
Definition CvtOptK    : Kind := STRUCT_TYPE { "unsigned" :: Bool ; "wide" :: Bool }.
Definition RoundOptK  : Kind := STRUCT_TYPE { "nx" :: Bool }.
(* Narrow conversion: `toNarrow` = own format -> narrow (else narrow -> own), `nidx` = the
 * narrow format's position in `narrow`. *)
Definition CvtNOptK (narrow : list FpFmt) : Kind :=
  STRUCT_TYPE { "toNarrow" :: Bool ; "nidx" :: Bit (NIdxSz narrow) }.

(* The operation: a tagged union of families with their options.  RISC-V instructions:
 *   add    {negB}            FADD / FSUB
 *   mul                      FMUL
 *   fma    {negProd; negAdd} FMADD {0;0} / FMSUB {0;1} / FNMSUB {1;0} / FNMADD {1;1}
 *   div / sqrt               FDIV / FSQRT
 *   minmax {isMax; nanProp}  FMIN / FMAX; Zfa FMINM / FMAXM (nanProp)
 *   sgnj   {mode}            FSGNJ (0) / FSGNJN (1) / FSGNJX (2)
 *   cmp    {mode; quiet}     FEQ (0) / FLT (1) / FLE (2); Zfa FLTQ / FLEQ (quiet)
 *   fclass                   FCLASS
 *   cvtFI  {unsigned; wide}  FCVT.{W,WU,L,LU}.fmt
 *   cvtIF  {unsigned; wide}  FCVT.fmt.{W,WU,L,LU}
 *   round  {nx}              Zfa FROUND / FROUNDNX
 *   cvtN   {toNarrow; nidx}  FCVT between the own format and a boxed narrow format *)
Definition FpuOpList (narrow : list FpFmt) : list (string * Kind) := [
  ("add", AddOptK) ; ("mul", Bit 0) ; ("fma", FmaOptK) ; ("div", Bit 0) ; ("sqrt", Bit 0) ;
  ("minmax", MinMaxOptK) ; ("sgnj", SgnjOptK) ; ("cmp", CmpOptK) ; ("fclass", Bit 0) ;
  ("cvtFI", CvtOptK) ; ("cvtIF", CvtOptK) ; ("round", RoundOptK) ; ("cvtN", CvtNOptK narrow) ].

Definition FpuOpK (narrow : list FpFmt) : Kind := TaggedUnion (FpuOpList narrow).

Definition FpuPktK (narrow : list FpFmt) : Kind :=
  STRUCT_TYPE {
    "op"   :: FpuOpK narrow ;
    "rm"   :: Bit 3 ;               (* static mode, or RmDyn *)
    "rs1"  :: Bit 5 ;
    "rs2"  :: Bit 5 ;
    "rs3"  :: Bit 5 ;
    "rd"   :: Bit 5
  }.

Section SpecFpu.
  (* Exponent mode of the floating-point core (`FpCore.v`), the first argument of every definition
   * that depends on it: `true` is the biased hardware model, `false` the unbiased reference model
   * (`FpCoreRef.v`); the two compute the same results (`Proof/FpCoreRefProof.v`). *)
  Variable bm : bool.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.

  Local Abbreviation PktK := (FpuPktK narrow).

  Definition FpuResK : Kind :=
    STRUCT_TYPE {
      "res"     :: Bit flen ;
      "xres"    :: Bit xlen ;
      "flags"   :: Bit 5 ;
      "writesF" :: Bool
    }.

  Section Exprs.
    Variable ty : Kind -> Type.

    (* NaN-box a narrow `fmtW G`-bit value into a register. *)
    Definition fpBox (G : FpFmt) (x : Expr ty (Bit (fmtW G))) : Expr ty (Bit flen) :=
      Or [ zext (fmtW G) flen x ; cst flen (2 ^ flen - 2 ^ fmtW G) ].

    (* Read a narrow `fmtW G`-bit operand: a value that is not properly NaN-boxed is the canonical NaN. *)
    Definition fpUnbox (G : FpFmt) (x : ty (Bit flen)) : Expr ty (Bit (fmtW G)) :=
      ITE (Eq (Srl (#x) (cst flen (fmtW G))) (cst flen (2 ^ (flen - fmtW G) - 1)))
          (trunc flen (fmtW G) (#x))
          (cst (fmtW G) (qnanMagZ (fmtE G) (fmtF G))).

    (* Results that go to an integer register. *)
    Definition opWritesXE (op : ty (FpuOpK narrow)) : Expr ty Bool :=
      Or [ #op `? "cvtFI" ; #op `? "cmp" ; #op `? "fclass" ].

    (* Box a narrow load / move into a register (`FLH`, `FMV.H.X`, ... for a narrow format `G`). *)
    Definition boxTo (G : FpFmt) (x : Expr ty (Bit (fmtW G))) : Expr ty (Bit flen) := fpBox G x.

    (* Zfa FLI: entry `idx` of the constant table in the own format (write it with `fpuWrite`;
     * for a narrow format `G`, `boxTo G (fliConstE (fmtE G) (fmtF G) _ idx)`). *)
    Definition fliConst (idx : Expr ty (Bit 5)) : Expr ty (Bit flen) := fliConstE (fmtE F) (fmtF F) ty idx.

    Definition isNarrowE (op : ty (FpuOpK narrow)) : Expr ty Bool := #op `? "cvtN".

    (* Decode the operation union into the core's flat record (options masked by their family). *)
    Definition decodeOp (op : ty (FpuOpK narrow)) : LetExpr ty FpOpDK :=
      LetE pAdd : AddOptK    <- #op `! "add" ;
      LetE pFma : FmaOptK    <- #op `! "fma" ;
      LetE pMm  : MinMaxOptK <- #op `! "minmax" ;
      LetE pSj  : SgnjOptK   <- #op `! "sgnj" ;
      LetE pCmp : CmpOptK    <- #op `! "cmp" ;
      LetE pFI  : CvtOptK    <- #op `! "cvtFI" ;
      LetE pIF  : CvtOptK    <- #op `! "cvtIF" ;
      LetE pRnd : RoundOptK  <- #op `! "round" ;
      RetE (STRUCT {
        "add"      ::= #op `? "add" ;
        "mul"      ::= #op `? "mul" ;
        "fma"      ::= #op `? "fma" ;
        "div"      ::= #op `? "div" ;
        "sqrt"     ::= #op `? "sqrt" ;
        "minmax"   ::= #op `? "minmax" ;
        "sgnj"     ::= #op `? "sgnj" ;
        "cmp"      ::= #op `? "cmp" ;
        "fclass"   ::= #op `? "fclass" ;
        "cvtFI"    ::= #op `? "cvtFI" ;
        "cvtIF"    ::= #op `? "cvtIF" ;
        "round"    ::= #op `? "round" ;
        "negB"     ::= And [ #op `? "add" ; ##pAdd`"negB" ] ;
        "negProd"  ::= And [ #op `? "fma" ; ##pFma`"negProd" ] ;
        "negAdd"   ::= And [ #op `? "fma" ; ##pFma`"negAdd" ] ;
        "isMax"    ::= And [ #op `? "minmax" ; ##pMm`"isMax" ] ;
        "nanProp"  ::= And [ #op `? "minmax" ; ##pMm`"nanProp" ] ;
        "mode"     ::= ITE (#op `? "sgnj") (##pSj`"mode") (ITE (#op `? "cmp") (##pCmp`"mode") (cst 2 0)) ;
        "quiet"    ::= And [ #op `? "cmp" ; ##pCmp`"quiet" ] ;
        "unsigned" ::= ITE (#op `? "cvtFI") (##pFI`"unsigned") (And [ #op `? "cvtIF" ; ##pIF`"unsigned" ]) ;
        "wide"     ::= ITE (#op `? "cvtFI") (##pFI`"wide") (And [ #op `? "cvtIF" ; ##pIF`"wide" ]) ;
        "nx"       ::= And [ #op `? "round" ; ##pRnd`"nx" ]
      } : Expr ty FpOpDK).

    (* An ordinary op in the own format `F`. *)
    Definition mainRes (op : ty (FpuOpK narrow)) (rm : ty (Bit 3)) (a b c : ty (Bit flen)) (x : ty (Bit xlen))
      : LetExpr ty FpuResK :=
      LETE od  : FpOpDK <- decodeOp op ;
      LetE req : FpReqK (fmtE F) (fmtF F) xlen <-
        STRUCT { "op" ::= #od ; "rm" ::= #rm ; "a" ::= #a ; "b" ::= #b ; "c" ::= #c ; "x" ::= #x } ;
      LETE o   : FpResK (fmtE F) (fmtF F) xlen <- fpuCompute bm (fmtE F) (fmtF F) xlen wlen ty req ;
      RetE (STRUCT {
        "res"     ::= ##o`"res" ;
        "xres"    ::= ##o`"xres" ;
        "flags"   ::= ##o`"flags" ;
        "writesF" ::= Not (opWritesXE op)
      } : Expr ty FpuResK).

    (* Conversion with the narrow format `G` (`toN`: own -> narrow, else narrow -> own). *)
    Definition narrowBlock (G : FpFmt) (toN : ty Bool) (rm : ty (Bit 3)) (a : ty (Bit flen))
      : LetExpr ty FpuResK :=
      LetE isFrom : Bool                     <- Not (#toN) ;
      LetE ag     : Bit (fmtW G)             <- fpUnbox G a ;
      LETE oF     : FpOutK (fmtE F) (fmtF F) <- cvtFF bm (fmtE G) (fmtF G) (fmtE F) (fmtF F) ty rm ag ;
      LetE rF     : Bit (fmtW F)             <- ##oF`"res" ;
      LETE oN     : FpOutK (fmtE G) (fmtF G) <- cvtFF bm (fmtE F) (fmtF F) (fmtE G) (fmtF G) ty rm a ;
      LetE rN     : Bit (fmtW G)             <- ##oN`"res" ;
      RetE (STRUCT {
        "res"     ::= ITE (#isFrom) (#rF) (fpBox G (#rN)) ;
        "xres"    ::= @cst ty xlen 0 ;
        "flags"   ::= ITE (#isFrom) (##oF`"flags") (##oN`"flags") ;
        "writesF" ::= Const ty Bool true
      } : Expr ty FpuResK).

    (* Select the narrow format `nidx` (entries from position `k` on). *)
    Fixpoint narrowSel (toN : ty Bool) (rm : ty (Bit 3)) (a : ty (Bit flen)) (nidx : ty (Bit (NIdxSz narrow)))
      (gs : list FpFmt) (k : nat) (acc : ty FpuResK) : LetExpr ty FpuResK :=
      match gs with
      | nil => RetE (#acc)
      | G :: rest =>
          LETE blk  : FpuResK <- narrowBlock G toN rm a ;
          LetE acc' : FpuResK <- ITE (Eq (#nidx) (cst (NIdxSz narrow) (Z.of_nat k))) (#blk) (#acc) ;
          narrowSel toN rm a nidx rest (S k) acc'
      end.
  End Exprs.

  Local Abbreviation AT := (fpuArchTree flen).

  Section Actions.
    Variable ty : Kind -> Type.

    Definition fpuRead (idx : Expr ty (Bit FprIdxSz)) : Action ty AT (Bit flen) :=
      archReadFpr flen ty idx.

    Definition fpuWrite (idx : Expr ty (Bit FprIdxSz)) (v : Expr ty (Bit flen)) : Action ty AT (Bit 0) :=
      Act (archWriteFpr flen ty idx v) ;
      archWriteFs flen ty (cst 2 FsDirty).

    Definition frmRead : Action ty AT (Bit 3) := archReadFrm flen ty.

    Definition frmWrite (v : Expr ty (Bit 3)) : Action ty AT (Bit 0) :=
      Act (archWriteFrm flen ty v) ;
      archWriteFs flen ty (cst 2 FsDirty).

    Definition fflagsRead : Action ty AT (Bit 5) := archReadFflags flen ty.

    Definition fflagsWrite (v : Expr ty (Bit 5)) : Action ty AT (Bit 0) :=
      Act (archWriteFflags flen ty v) ;
      archWriteFs flen ty (cst 2 FsDirty).

    (* `fcsr[7:0]` = {frm, fflags}. *)
    Definition fcsrRead : Action ty AT (Bit 8) :=
      LetA frm : Bit 3 <- archReadFrm flen ty ;
      LetA ff  : Bit 5 <- archReadFflags flen ty ;
      Return (Concat (#frm) (#ff)).

    Definition fcsrWrite (v : Expr ty (Bit 8)) : Action ty AT (Bit 0) :=
      Act (archWriteFrm flen ty (TruncMsb 3 5 v)) ;
      Act (archWriteFflags flen ty (TruncLsb 3 5 v)) ;
      archWriteFs flen ty (cst 2 FsDirty).

    Definition fsRead : Action ty AT (Bit 2) := archReadFs flen ty.

    Definition fsWrite (v : Expr ty (Bit 2)) : Action ty AT (Bit 0) := archWriteFs flen ty v.

    (* The rounding mode of a packet: DYN -> `frm`. *)
    Definition resolveRm (pktRm frm : Expr ty (Bit 3)) : Expr ty (Bit 3) :=
      ITE (Eq pktRm (cst 3 RmDyn)) frm pktRm.

    Definition FpuRes0 : Expr ty FpuResK :=
      STRUCT { "res" ::= @cst ty flen 0 ; "xres" ::= @cst ty xlen 0 ;
               "flags" ::= @cst ty 5 0 ; "writesF" ::= Const ty Bool false }.

    (* The result of one instruction from its operand values and resolved rounding mode. *)
    Definition execCompute (pkt : ty PktK) (rm : ty (Bit 3)) (a b c : ty (Bit flen)) (x : ty (Bit xlen))
      : LetExpr ty FpuResK :=
      LetE op   : FpuOpK narrow       <- ##pkt`"op" ;
      LETE m    : FpuResK             <- mainRes ty op rm a b c x ;
      LetE pN   : CvtNOptK narrow     <- #op `! "cvtN" ;
      LetE toN  : Bool                <- ##pN`"toNarrow" ;
      LetE nidx : Bit (NIdxSz narrow) <- ##pN`"nidx" ;
      LetE r0   : FpuResK             <- FpuRes0 ;
      LETE n    : FpuResK             <- narrowSel ty toN rm a nidx narrow 0 r0 ;
      RetE (ITE (isNarrowE ty op) (#n) (#m)).

    Definition fpuExec (pkt : ty PktK) (xval : ty (Bit xlen)) : Action ty AT (Bit xlen) :=
      LetA a   : Bit flen <- archReadFpr flen ty (##pkt`"rs1") ;
      LetA b   : Bit flen <- archReadFpr flen ty (##pkt`"rs2") ;
      LetA c   : Bit flen <- archReadFpr flen ty (##pkt`"rs3") ;
      LetA frm : Bit 3    <- archReadFrm flen ty ;
      Let rm   : Bit 3    <- resolveRm (##pkt`"rm") (#frm) ;
      LetL r   : FpuResK  <- execCompute pkt rm a b c xval ;
      If (##r`"writesF") Then (archWriteFpr flen ty (##pkt`"rd") (##r`"res")) Else Retv ;
      LetA ff  : Bit 5    <- archReadFflags flen ty ;
      Act (archWriteFflags flen ty (Or [ #ff ; ##r`"flags" ])) ;
      Act (archWriteFs flen ty (cst 2 FsDirty)) ;
      Return (##r`"xres").
  End Actions.

  (* --- Gallina semantics of the actions, for replay by a parent proof --- *)
  Section Semantics.
    Local Abbreviation St := (ArchSt flen).

    Definition dirtyZ : bits 2 := Zmod.of_Z _ FsDirty.

    Definition pktRs1 (pkt : type PktK) : bits FprIdxSz := pkt @% "rs1".
    Definition pktRs2 (pkt : type PktK) : bits FprIdxSz := pkt @% "rs2".
    Definition pktRs3 (pkt : type PktK) : bits FprIdxSz := pkt @% "rs3".
    Definition pktRd  (pkt : type PktK) : bits FprIdxSz := pkt @% "rd".

    Definition rmOf (pkt : type PktK) (frm : bits 3) : bits 3 :=
      evalExpr (resolveRm type (Var type (Bit 3) (pkt @% "rm")) (Var type (Bit 3) frm)).

    (* The result of `pkt` with the given operand values and resolved rounding mode. *)
    Definition execResOf (pkt : type PktK) (rm : bits 3) (a b c : bits flen) (x : bits xlen) : type FpuResK :=
      evalLetExpr (execCompute type pkt rm a b c x).

    (* The result of `pkt` from state `s`. *)
    Definition execRes (s : St) (pkt : type PktK) (x : bits xlen) : type FpuResK :=
      execResOf pkt (rmOf pkt (archFrm flen s))
                (archFpr flen s (pktRs1 pkt)) (archFpr flen s (pktRs2 pkt)) (archFpr flen s (pktRs3 pkt)) x.

    (* Applying a result to the state: write `rd` (unless the result goes to an integer register),
     * OR the flags, set `fs` to Dirty. *)
    Definition applyRes (s : St) (rd : bits FprIdxSz) (r : type FpuResK) : St :=
      let s1 := if r @% "writesF" then archSetFpr flen s rd (r @% "res") else s in
      let s2 := archSetFflags flen s1 (Zmod.or (archFflags flen s) (r @% "flags")) in
      archSetFs flen s2 dirtyZ.

    Definition execSem (s : St) (pkt : type PktK) (x : bits xlen) : St :=
      applyRes s (pktRd pkt) (execRes s pkt x).

    Definition writeSem (s : St) (idx : bits FprIdxSz) (v : bits flen) : St :=
      archSetFs flen (archSetFpr flen s idx v) dirtyZ.

    Definition frmWriteSem (s : St) (v : bits 3) : St := archSetFs flen (archSetFrm flen s v) dirtyZ.
    Definition fflagsWriteSem (s : St) (v : bits 5) : St := archSetFs flen (archSetFflags flen s v) dirtyZ.
    Definition fcsrWriteSem (s : St) (v : bits 8) : St :=
      archSetFs flen (archSetFflags flen (archSetFrm flen s (evalExpr (TruncMsb 3 5 (Var type (Bit 8) v))))
                                       (evalExpr (TruncLsb 3 5 (Var type (Bit 8) v)))) dirtyZ.
    Definition fsWriteSem (s : St) (v : bits 2) : St := archSetFs flen s v.
    Definition fcsrOf (s : St) : bits 8 :=
      evalExpr (Concat (Var type (Bit 3) (archFrm flen s)) (Var type (Bit 5) (archFflags flen s))).
  End Semantics.
End SpecFpu.

Arguments pktRs1 {narrow} pkt.
Arguments pktRs2 {narrow} pkt.
Arguments pktRs3 {narrow} pkt.
Arguments pktRd {narrow} pkt.
Arguments rmOf {narrow} pkt frm.
