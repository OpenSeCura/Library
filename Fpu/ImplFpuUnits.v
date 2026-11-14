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
 * Staged FPU execution units (`ImplFpuUnits.v`), one format `(e, f)`.
 *
 * Each unit runs the algorithm of `FpCore.v` as `finish (step^n (init req))` on a generic
 * controller of `ImplStaged.v`:
 *
 * - Pipe unit (`stagedPipe`, `mul_stages` stages): every op except DIV, SQRT and CVTFF.
 *   `init` = `pipeInfoOf` + operands of the significand product, each stage = `mul_bps` bits of the
 *   unsigned shift-and-add multiplier (`IntMul.v`), `finish` = `pipeFinishCore`.  The multiplier
 *   width `mul_stages * mul_bps` must be at least `p = f + 1` (the significands are
 *   zero-extended), so any number of stages works for any format.
 * - Divide unit (`stagedIter`, `f + 3` iterations): restoring division of the significands,
 *   one quotient bit per iteration; `finish` = `divFinishCore` (spec: `Div` / `Rem`).
 * - Square-root unit (`stagedIter`, `f + 3` iterations): `sqrtInit` / `sqrtStep` / `sqrtFinish`
 *   of `FpCore.v`.
 *
 * See `Proof/FpuUnitsProof.v`.
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Fpu Require Import FpUtil FpCore IntMul ImplStaged.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. PIPE UNIT
 * =========================================================================== *)

Definition PipeStateK (e f xlen : Z) (mw : nat) : Kind :=
  STRUCT_TYPE {
    "info"    :: PipeInfoK e f xlen ;
    "shiftOp" :: Bit (dataLen mw) ;
    "extOp2"  :: Bit (dataLen mw + dataLen mw) ;
    "mulAcc"  :: Bit (dataLen mw + dataLen mw)
  }.

Section PipeUnit.
  Variable e f xlen : Z.
  Variable mul_stages mul_bps : nat.

  Local Abbreviation mw := (mul_stages * mul_bps)%nat.
  Local Abbreviation dm := (dataLen mw).
  Local Abbreviation SK := (PipeStateK e f xlen mw).

  Definition pipeInit (ty : Kind -> Type) (req : ty (FpReqK e f xlen)) : LetExpr ty SK :=
    LETE info : PipeInfoK e f xlen <- pipeInfoOf true e f xlen ty req ;
    LetE ua   : FpUnpK e f     <- ##info`"ua" ;
    LetE ub   : FpUnpK e f     <- ##info`"ub" ;
    LetE siga : Bit (f + 1)    <- ##ua`"sig" ;
    LetE sigb : Bit (f + 1)    <- ##ub`"sig" ;
    LetE op1  : Bit dm         <- zext (f + 1) dm (#siga) ;
    LetE op2  : Bit dm         <- zext (f + 1) dm (#sigb) ;
    LetE ext2 : Bit (dm + dm)  <- ZeroExtend dm (#op2) ;
    LetE acc0 : Bit (dm + dm)  <- Const ty (Bit (dm + dm)) Zmod.zero ;
    @RetE ty SK (STRUCT {
      "info"    ::= #info ;
      "shiftOp" ::= #op1 ;
      "extOp2"  ::= #ext2 ;
      "mulAcc"  ::= #acc0
    }).

  Definition pipeStep (ty : Kind -> Type) (st : ty SK) : LetExpr ty SK :=
    LetE shiftOp : Bit dm         <- ##st`"shiftOp" ;
    LetE extOp2  : Bit (dm + dm)  <- ##st`"extOp2" ;
    LetE mulAcc  : Bit (dm + dm)  <- ##st`"mulAcc" ;
    LETE core    : MulCoreState dm <- @mulMultiStep mw ty mul_bps shiftOp extOp2 mulAcc ;
    LetE nShift  : Bit dm         <- ##core`"shiftOp" ;
    LetE nAcc    : Bit (dm + dm)  <- ##core`"mulAcc" ;
    @RetE ty SK ((##st `{ "shiftOp" <- #nShift }) `{ "mulAcc" <- #nAcc }).

  Definition pipeFinish (ty : Kind -> Type) (st : ty SK) : LetExpr ty (FpResK e f xlen) :=
    LetE info : PipeInfoK e f xlen <- ##st`"info" ;
    LetE prod : Bit (2 * f + 2)    <- trunc (dm + dm) (2 * f + 2) (##st`"mulAcc") ;
    pipeFinishCore true e f xlen ty info prod.

  Definition fpPipeTree : Tree Elem := stagedPipeTree SK mul_stages.

  Definition fpPipeCanEnq (ty : Kind -> Type) := stagedPipeCanEnq SK mul_stages ty.

  Definition fpPipeEnq (ty : Kind -> Type) (req : ty (FpReqK e f xlen)) :=
    @stagedPipeEnq (FpReqK e f xlen) SK mul_stages pipeInit ty req.

  Definition fpPipeRules (ty : Kind -> Type) := stagedPipeAllStageRules SK mul_stages pipeStep ty.

  Definition fpPipeFirst (ty : Kind -> Type) := stagedPipeFirst SK (FpResK e f xlen) mul_stages pipeFinish ty.

  Definition fpPipeDeq (ty : Kind -> Type) := stagedPipeDeq SK mul_stages ty.

  Definition fpPipeMod : Mod fpPipeTree := stagedPipeMod SK mul_stages pipeStep.
End PipeUnit.

(* ===========================================================================
 * 2. DIVIDE UNIT
 * =========================================================================== *)

Definition DivStateK (e f : Z) : Kind :=
  STRUCT_TYPE {
    "info" :: DivInfoK e f ;
    "rem"  :: Bit (f + 2) ;   (* twice the partial remainder, < 2 * den *)
    "den"  :: Bit (f + 1) ;   (* divisor significand *)
    "quot" :: Bit (f + 3)     (* partial quotient *)
  }.

Section DivUnit.
  Variable e f xlen : Z.

  Local Abbreviation SK := (DivStateK e f).

  Definition divSteps : nat := Z.to_nat (f + 3).

  Definition divInit (ty : Kind -> Type) (req : ty (FpReqK e f xlen)) : LetExpr ty SK :=
    LETE info  : DivInfoK e f <- divInfoOf true e f xlen ty req ;
    LetE ua    : FpUnpK e f   <- ##info`"ua" ;
    LetE ub    : FpUnpK e f   <- ##info`"ub" ;
    LetE siga  : Bit (f + 1)  <- ##ua`"sig" ;
    LetE sigb  : Bit (f + 1)  <- ##ub`"sig" ;
    LetE rem0  : Bit (f + 2)  <- zext (f + 1) (f + 2) (#siga) ;
    LetE quot0 : Bit (f + 3)  <- cst (f + 3) 0 ;
    @RetE ty SK (STRUCT {
      "info" ::= #info ;
      "rem"  ::= #rem0 ;
      "den"  ::= #sigb ;
      "quot" ::= #quot0
    }).

  (* One quotient bit: subtract the divisor if it fits, then shift the remainder. *)
  Definition divStep (ty : Kind -> Type) (st : ty SK) : LetExpr ty SK :=
    LetE rem  : Bit (f + 2) <- ##st`"rem" ;
    LetE den  : Bit (f + 1) <- ##st`"den" ;
    LetE quot : Bit (f + 3) <- ##st`"quot" ;
    LetE denx : Bit (f + 2) <- zext (f + 1) (f + 2) (#den) ;
    LetE ge   : Bool        <- Not (Ult (#rem) (#denx)) ;
    LetE rem1 : Bit (f + 2) <- ITE (#ge) (Sub (#rem) (#denx)) (#rem) ;
    @RetE ty SK
      ((##st `{ "rem" <- Sll (#rem1) (cst (f + 2) 1) })
             `{ "quot" <- Or [ Sll (#quot) (cst (f + 3) 1) ; ITE (#ge) (cst (f + 3) 1) (cst (f + 3) 0) ] }).

  Definition divFinish (ty : Kind -> Type) (st : ty SK) : LetExpr ty (FpOutK e f) :=
    LetE info : DivInfoK e f <- ##st`"info" ;
    LetE q    : Bit (f + 3)  <- ##st`"quot" ;
    LetE stk  : Bool         <- isNotZero (##st`"rem") ;
    divFinishCore true e f ty info q stk.

  Definition divStepsConst (ty : Kind -> Type) (_ : ty (FpReqK e f xlen))
    : LetExpr ty (Bit (iterStepsSz divSteps)) :=
    RetE (Const ty (Bit (iterStepsSz divSteps)) (bits.of_Z (iterStepsSz divSteps) (Z.of_nat divSteps))).

  Definition fpDivTree : Tree Elem := stagedIterTree SK divSteps.

  Definition fpDivCanEnq (ty : Kind -> Type) := stagedIterCanEnq SK divSteps ty.

  Definition fpDivEnq (ty : Kind -> Type) (req : ty (FpReqK e f xlen)) :=
    @stagedIterEnq (FpReqK e f xlen) SK divSteps divStepsConst divInit ty req.

  Definition fpDivStepRule (ty : Kind -> Type) := stagedIterStep SK divSteps divStep ty.

  Definition fpDivFirst (ty : Kind -> Type) := stagedIterFirst SK (FpOutK e f) divSteps divFinish ty.

  Definition fpDivDeq (ty : Kind -> Type) := stagedIterDeq SK divSteps ty.

  Definition fpDivMod : Mod fpDivTree := stagedIterMod SK divSteps divStep.
End DivUnit.

(* ===========================================================================
 * 3. SQUARE-ROOT UNIT
 * =========================================================================== *)

Section SqrtUnit.
  Variable e f xlen : Z.

  Local Abbreviation SK := (SqrtStateK e f).
  Local Abbreviation nSteps := (sqrtSteps f).

  Definition sqrtStepsConst (ty : Kind -> Type) (_ : ty (FpReqK e f xlen))
    : LetExpr ty (Bit (iterStepsSz nSteps)) :=
    RetE (Const ty (Bit (iterStepsSz nSteps)) (bits.of_Z (iterStepsSz nSteps) (Z.of_nat nSteps))).

  Definition fpSqrtTree : Tree Elem := stagedIterTree SK nSteps.

  Definition fpSqrtCanEnq (ty : Kind -> Type) := stagedIterCanEnq SK nSteps ty.

  Definition fpSqrtEnq (ty : Kind -> Type) (req : ty (FpReqK e f xlen)) :=
    @stagedIterEnq (FpReqK e f xlen) SK nSteps sqrtStepsConst (sqrtInit true e f xlen) ty req.

  Definition fpSqrtStepRule (ty : Kind -> Type) := stagedIterStep SK nSteps (sqrtStep e f) ty.

  Definition fpSqrtFirst (ty : Kind -> Type) := stagedIterFirst SK (FpOutK e f) nSteps (sqrtFinish true e f) ty.

  Definition fpSqrtDeq (ty : Kind -> Type) := stagedIterDeq SK nSteps ty.

  Definition fpSqrtMod : Mod fpSqrtTree := stagedIterMod SK nSteps (sqrtStep e f).
End SqrtUnit.
