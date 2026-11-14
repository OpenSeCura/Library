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
 * Evaluation lemmas for the helpers of `FpUtil.v` (`FpUtilLemmas.v`).
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil IntMulProof.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Lemma positive_cast_refl : forall (n : positive) (P : positive -> Type) (pf : n = n) (v : P n),
  @positive_cast P n n pf v = v.
Proof.
  induction n as [n IH | n IH |]; intros P pf v; cbn;
    [apply (IH (fun p => P (xI p))) | apply (IH (fun p => P (xO p))) | reflexivity].
Qed.

Lemma Z_cast_refl : forall (n : Z) (P : Z -> Type) (pf : n = n) (v : P n), @Z_cast P n n pf v = v.
Proof.
  intros [| n | n] P pf v; cbn;
    [reflexivity | apply (positive_cast_refl n (fun p => P (Zpos p))) | apply (positive_cast_refl n (fun p => P (Zneg p)))].
Qed.

Lemma castBits_refl : forall (ty : Kind -> Type) (n : Z) (pf : n = n) (x : Expr ty (Bit n)),
  castBits pf x = x.
Proof. intros ty n pf x; unfold castBits; apply (Z_cast_refl n (fun n => Expr ty (Bit n))). Qed.

Lemma unsigned_castBits : forall (ni no : Z) (pf : ni = no) (x : Expr type (Bit ni)),
  Zmod.unsigned (evalExpr (castBits pf x)) = Zmod.unsigned (evalExpr x).
Proof. intros ni no pf x; subst no; rewrite castBits_refl; reflexivity. Qed.

Lemma unsigned_cst : forall w v, 0 <= w ->
  Zmod.unsigned (evalExpr (@cst type w v)) = v mod 2 ^ w.
Proof. intros w v Hw; cbn; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_zext : forall (i o : Z) (x : Expr type (Bit i)),
  0 <= i <= o ->
  Zmod.unsigned (evalExpr (zext i o x)) = Zmod.unsigned (evalExpr x).
Proof.
  intros i o x Hio; unfold zext.
  rewrite unsigned_castBits.
  cbn [evalExpr ZeroExtend].
  rewrite unsigned_app_arith by lia.
  rewrite Zmod.unsigned_0; lia.
Qed.

Lemma unsigned_trunc : forall (i o : Z) (x : Expr type (Bit i)),
  0 <= o <= i ->
  Zmod.unsigned (evalExpr (trunc i o x)) = Zmod.unsigned (evalExpr x) mod 2 ^ o.
Proof.
  intros i o x Hio; unfold trunc.
  cbn [evalExpr].
  rewrite unsigned_firstn by lia.
  rewrite unsigned_castBits; reflexivity.
Qed.

Lemma bits_unsigned_bound : forall (w : Z) (x : bits w), 0 <= w -> 0 <= Zmod.unsigned x < 2 ^ w.
Proof. intros w x Hw; apply bits.unsigned_range; lia. Qed.

(* `castBits` with symbolic widths blocks evaluation: congruence lemmas. *)
Lemma evalExpr_castBits_congr : forall (ni no : Z) (pf : ni = no) (x y : Expr type (Bit ni)),
  evalExpr x = evalExpr y -> evalExpr (castBits pf x) = evalExpr (castBits pf y).
Proof. intros ni no pf x y H; subst no; rewrite !castBits_refl; exact H. Qed.

Lemma evalExpr_trunc_congr : forall (i o : Z) (x y : Expr type (Bit i)),
  evalExpr x = evalExpr y -> evalExpr (trunc i o x) = evalExpr (trunc i o y).
Proof.
  intros i o x y H; unfold trunc; cbn [evalExpr].
  rewrite (evalExpr_castBits_congr _ _ (trunc_pf i o) x y H); reflexivity.
Qed.

Lemma evalExpr_zext_congr : forall (i o : Z) (x y : Expr type (Bit i)),
  evalExpr x = evalExpr y -> evalExpr (zext i o x) = evalExpr (zext i o y).
Proof.
  intros i o x y H; unfold zext.
  apply evalExpr_castBits_congr; cbn [evalExpr ZeroExtend]; rewrite H; reflexivity.
Qed.

Lemma unsigned_ZeroExtend : forall (m i : Z) (x : Expr type (Bit i)),
  0 <= i -> 0 <= m ->
  Zmod.unsigned (evalExpr (ZeroExtend m x)) = Zmod.unsigned (evalExpr x).
Proof.
  intros m i x Hi Hm; cbn [evalExpr ZeroExtend].
  rewrite unsigned_app_arith by lia.
  rewrite Zmod.unsigned_0; lia.
Qed.

Lemma evalExpr_Var : forall (k : Kind) (v : type k), evalExpr (Var type k v) = v.
Proof. reflexivity. Qed.

Lemma testbit_ge_pow2 : forall x n, 0 <= x -> 0 <= n -> Z.testbit x n = true -> 2 ^ n <= x.
Proof.
  intros x n Hx Hn Hb.
  destruct (Z_lt_le_dec x (2 ^ n)) as [Hlt | Hge]; [| exact Hge].
  apply Z.testbit_true in Hb; [| exact Hn].
  rewrite Z.div_small in Hb by lia; discriminate.
Qed.

Lemma unsigned_or_pow2_ge : forall (w i : Z) (a : bits w),
  0 <= i < w ->
  2 ^ i <= Zmod.unsigned (Zmod.or a (Zmod.of_Z (2 ^ w) (2 ^ i))).
Proof.
  intros w i a Hi.
  rewrite bits.unsigned_or, Zmod.unsigned_of_Z.
  assert (Hp : 2 ^ i < 2 ^ w) by (apply Z.pow_lt_mono_r; lia).
  rewrite (Z.mod_small (2 ^ i)) by (split; [apply Z.pow_nonneg; lia | exact Hp]).
  pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
  apply testbit_ge_pow2; [apply Z.lor_nonneg; split; [lia | apply Z.pow_nonneg; lia] | lia |].
  rewrite Z.lor_spec, Z.pow2_bits_true by lia; apply orb_true_r.
Qed.

Lemma evalExpr_isNotZero_bits : forall (w : Z) (x : Expr type (Bit w)),
  evalExpr (isNotZero x) = negb (Zmod.unsigned (evalExpr x) =? 0).
Proof.
  intros w x; cbn [evalExpr isNotZero isZero evalNot isEq KindCustomInd getDefault].
  f_equal.
  destruct (Zmod.eqb_spec (evalExpr x) Zmod.zero) as [H | H].
  - rewrite H, Zmod.unsigned_0; reflexivity.
  - symmetry; apply Z.eqb_neq; intros H0; apply H.
    apply Zmod.unsigned_inj; rewrite H0, Zmod.unsigned_0; reflexivity.
Qed.
