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
 * Unsigned shift-and-add multiplier core (`IntMul.v`).
 *
 * Copied from `cheriot/Impl/ImplMulDiv.v` (the width-generic, unsigned part only).
 * `mulMultiStep input_width input_width op1 (ZeroExtend op2) 0` computes the full
 * `2 * input_width`-bit unsigned product `op1 * op2`, one bit of `op1` per `mulBitStep`
 * (MSB first).  The step is independent of the bit index, so it can be used verbatim as
 * the `stepFn` of a pipelined or iterative staged controller (`ImplStaged.v`).
 * See `Proof/IntMulProof.v`.
 *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations.

Set Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Definition dataLen (input_width : nat) : Z :=
  Z.of_nat input_width.

Section ParameterizedTypes.
  Variable d : Z.

  Definition MulCoreState : Kind :=
    STRUCT_TYPE {
      "shiftOp" :: Bit d ;
      "mulAcc"  :: Bit (d + d)
    }.

End ParameterizedTypes.

Section StageIndependentCombinational.
  Variable input_width : nat.
  Local Abbreviation d := (dataLen input_width).

  Variable ty : Kind -> Type.

  Definition mulBitStep
    (shiftOp : ty (Bit d)) (extOp2 : ty (Bit (d + d))) (mulAcc : ty (Bit (d + d)))
    : LetExpr ty (MulCoreState d) :=
    LetE msbIdx    : Bit d       <- Const ty (Bit d) (bits.of_Z d (d - 1)) ;
    LetE mulBit_d  : Bit d       <- And [ Srl #shiftOp #msbIdx ; $1 ] ;
    LetE mulBit    : Bool        <- isNotZero #mulBit_d ;
    LetE nextShift : Bit d       <- Sll #shiftOp (Const ty (Bit 1) (bits.of_Z 1 1)) ;
    LetE accShift  : Bit (d + d) <- Sll #mulAcc (Const ty (Bit 1) (bits.of_Z 1 1)) ;
    LetE nextAcc   : Bit (d + d) <- ITE #mulBit (Add [ #accShift ; #extOp2 ]) #accShift ;
    @RetE ty (MulCoreState d) (STRUCT {
      "shiftOp" ::= #nextShift ;
      "mulAcc"  ::= #nextAcc
    }).

  Fixpoint mulMultiStep (count : nat)
    (shiftOp : ty (Bit d)) (extOp2 : ty (Bit (d + d))) (mulAcc : ty (Bit (d + d)))
    : LetExpr ty (MulCoreState d) :=
    match count with
    | 0%nat =>
        @RetE ty (MulCoreState d) (STRUCT {
          "shiftOp" ::= #shiftOp ;
          "mulAcc"  ::= #mulAcc
        })
    | S remCount =>
        LETE stepOut : MulCoreState d <- mulBitStep shiftOp extOp2 mulAcc ;
        LetE nShift  : Bit d          <- ##stepOut`"shiftOp" ;
        LetE nAcc    : Bit (d + d)    <- ##stepOut`"mulAcc" ;
        mulMultiStep remCount nShift extOp2 nAcc
    end.

End StageIndependentCombinational.
