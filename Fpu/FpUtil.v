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
 * Width-generic expression helpers for the FPU (`FpUtil.v`).
 *
 * - `zext i o` / `sext i o` / `trunc i o`: zero-extend / sign-extend / truncate a `Bit i` to a `Bit o` for symbolic widths
 *   (the width equation is discharged with `castBits`, which reduces on concrete widths).
 * - `cst w v`: the `w`-bit constant `v mod 2^w`.
 * - `bitSet x i`: bit `i` of a variable `x`.
 * - `Slt`: signed (two's complement) less-than.
 * - `clz w m x`: count of leading zeros of the `w`-bit variable `x`, as an `m`-bit value
 *   (`w` when `x = 0`).
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations.

Set Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Lemma zext_pf : forall i o : Z, i + (o - i) = o.
Proof. intros; lia. Qed.

Lemma trunc_pf : forall i o : Z, i = o + (i - o).
Proof. intros; lia. Qed.

Section Helpers.
  Variable ty : Kind -> Type.

  Definition cst (w v : Z) : Expr ty (Bit w) := Const ty (Bit w) (Zmod.of_Z _ v).

  Definition zext (i o : Z) (x : Expr ty (Bit i)) : Expr ty (Bit o) :=
    castBits (zext_pf i o) (ZeroExtend (o - i) x).

  Definition sext (i o : Z) (x : Expr ty (Bit i)) : Expr ty (Bit o) :=
    castBits (zext_pf i o) (SignExtend (o - i) x).

  Definition trunc (i o : Z) (x : Expr ty (Bit i)) : Expr ty (Bit o) :=
    TruncLsb (i - o) o (castBits (trunc_pf i o) x).

  Definition bitSet (w : Z) (x : ty (Bit w)) (i : Z) : Expr ty Bool :=
    isNotZero (And [ Var ty (Bit w) x ; cst w (2 ^ i) ]).

  Definition Slt (w : Z) (a b : Expr ty (Bit w)) : Expr ty Bool :=
    Ult (Xor [ a ; cst w (2 ^ (w - 1)) ]) (Xor [ b ; cst w (2 ^ (w - 1)) ]).

  Definition clz (w m : Z) (x : ty (Bit w)) : Expr ty (Bit m) :=
    fold_left (fun acc i => ITE (bitSet x i) (cst m (w - 1 - i)) acc)
              (map Z.of_nat (seq 0 (Z.to_nat w)))
              (cst m w).

  Definition boolBit (b : Expr ty Bool) : Expr ty (Bit 1) :=
    ITE b (cst 1 1) (cst 1 0).
End Helpers.

Arguments cst {ty} w v.
Arguments zext {ty} i o x.
Arguments trunc {ty} i o x.
Arguments sext {ty} i o x.
Arguments bitSet {ty w} x i.
Arguments Slt {ty w} a b.
Arguments clz {ty} w m x.
Arguments boolBit {ty} b.
