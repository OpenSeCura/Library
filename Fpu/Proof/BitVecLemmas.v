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
 * Bit-vector lemmas for the FPU scoreboard (`BitVecLemmas.v`): `bitTestE`, `bitSetE`,
 * `bitClrE` of `ImplFpu.v` in terms of `bitOf`.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpuArch ImplFpu.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.

Lemma idx_range : forall (r : bits FprIdxSz), 0 <= Zmod.unsigned r < RegVecSz.
Proof. intros r; pose proof (bits.unsigned_range r ltac:(unfold FprIdxSz; lia)); unfold FprIdxSz, RegVecSz in *; cbn in *; lia. Qed.

Lemma tb_ones32 : forall j, 0 <= j < RegVecSz ->
  Z.testbit (Zmod.unsigned (Zmod.of_Z (2 ^ RegVecSz) (-1))) j = true.
Proof.
  intros j Hj; rewrite Zmod.of_Z_m1, bits.testbit_m1 by (unfold RegVecSz; lia).
  apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma tb_and : forall (a b : bits RegVecSz) j,
  Z.testbit (Zmod.unsigned (Zmod.and a b)) j = Z.testbit (Zmod.unsigned a) j && Z.testbit (Zmod.unsigned b) j.
Proof. intros; rewrite bits.unsigned_and, Z.land_spec; reflexivity. Qed.

Lemma tb_or : forall (a b : bits RegVecSz) j,
  Z.testbit (Zmod.unsigned (Zmod.or a b)) j = Z.testbit (Zmod.unsigned a) j || Z.testbit (Zmod.unsigned b) j.
Proof. intros; change (Zmod.unsigned (Zmod.or a b)) with (Zmod.to_Z (Zmod.or a b)); rewrite bits.unsigned_or, Z.lor_spec; reflexivity. Qed.

Lemma tb_not : forall (a : bits RegVecSz) j, 0 <= j < RegVecSz ->
  Z.testbit (Zmod.unsigned (Zmod.not a)) j = negb (Z.testbit (Zmod.unsigned a) j).
Proof.
  intros a j Hj; change (Zmod.unsigned (Zmod.not a)) with (Zmod.to_Z (Zmod.not a)).
  rewrite bits.unsigned_not, Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
  replace (j <? RegVecSz) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity.
Qed.

Lemma tb_mask : forall (i : bits FprIdxSz) j, 0 <= j < RegVecSz ->
  Z.testbit (Zmod.unsigned (evalExpr (bitMaskE type (Var type (Bit FprIdxSz) i)))) j = (Zmod.unsigned i =? j).
Proof.
  intros i j Hj; pose proof (idx_range i) as Hi.
  cbn [evalExpr bitMaskE cst]; change (Zmod.unsigned (Zmod.slu (Zmod.of_Z (2 ^ RegVecSz) 1) (Zmod.to_Z i)))
    with (Zmod.to_Z (Zmod.slu (Zmod.of_Z (2 ^ RegVecSz) 1) (Zmod.to_Z i))).
  rewrite bits.unsigned_slu, Z.mod_pow2_bits_low by lia.
  change (Zmod.to_Z (Zmod.of_Z (2 ^ RegVecSz) 1)) with 1.
  rewrite Z.shiftl_1_l, Z.pow2_bits_eqb by lia; reflexivity.
Qed.

Lemma tb_high : forall (a : bits RegVecSz) j, RegVecSz <= j -> Z.testbit (Zmod.unsigned a) j = false.
Proof. intros; apply bits.testbit_high; unfold RegVecSz in *; lia. Qed.

Lemma bits32_eq_tb : forall (a b : bits RegVecSz),
  (forall j, 0 <= j < RegVecSz -> Z.testbit (Zmod.unsigned a) j = Z.testbit (Zmod.unsigned b) j) -> a = b.
Proof.
  intros a b H; apply Zmod.unsigned_inj; apply Z.bits_inj; intros j.
  destruct (Z.ltb_spec j 0) as [Hn | Hn]; [rewrite !Z.testbit_neg_r by lia; reflexivity |].
  destruct (Z.ltb_spec j RegVecSz) as [Hl | Hl]; [apply H; lia | rewrite !tb_high by lia; reflexivity].
Qed.

Section BitVec.
  Variable w : bits RegVecSz.
  Variable i : bits FprIdxSz.

  Lemma evalExpr_bitTestE : evalExpr (bitTestE type (Var type (Bit RegVecSz) w) (Var type (Bit FprIdxSz) i)) = bitOf w i.
  Proof.
    pose proof (idx_range i) as Hi; unfold bitTestE, bitOf.
    cbn [evalExpr fold_left map evalNot isEq KindCustomInd InvDefault evalAndBinary evalBinary cst].
    set (m := evalExpr (bitMaskE type (Var type (Bit FprIdxSz) i))).
    set (x := Zmod.and (Zmod.and (Zmod.of_Z (2 ^ RegVecSz) (-1)) w) m).
    assert (Hx : forall j, 0 <= j < RegVecSz -> Z.testbit (Zmod.unsigned x) j =
                 Z.testbit (Zmod.unsigned w) j && (Zmod.unsigned i =? j)).
    { intros j Hj; unfold x, m; rewrite !tb_and, tb_ones32, tb_mask by exact Hj; reflexivity. }
    destruct (Z.testbit (Zmod.unsigned w) (Zmod.unsigned i)) eqn:Hw.
    - destruct (Zmod.eqb_spec x (Zmod.of_Z (2 ^ RegVecSz) 0)) as [H0 | _]; [| reflexivity].
      exfalso; specialize (Hx (Zmod.unsigned i) Hi); rewrite H0, Hw, Z.eqb_refl in Hx.
      change (Zmod.unsigned (Zmod.of_Z (2 ^ RegVecSz) 0)) with 0 in Hx; rewrite Z.testbit_0_l in Hx; discriminate.
    - replace x with (Zmod.of_Z (2 ^ RegVecSz) 0); [rewrite Zmod.eqb_refl; reflexivity |].
      apply bits32_eq_tb; intros j Hj; rewrite Hx by exact Hj.
      change (Zmod.unsigned (Zmod.of_Z (2 ^ RegVecSz) 0)) with 0; rewrite Z.testbit_0_l.
      destruct (Z.eqb_spec (Zmod.unsigned i) j) as [<- | _]; [rewrite Hw |]; rewrite ?andb_false_r; reflexivity.
  Qed.

  Lemma bitOf_set : forall j,
    bitOf (evalExpr (bitSetE type (Var type (Bit RegVecSz) w) (Var type (Bit FprIdxSz) i))) j = if Zmod.eqb j i then true else bitOf w j.
  Proof.
    intros j; pose proof (idx_range j) as Hj; unfold bitOf, bitSetE.
    cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
    rewrite !tb_or, tb_mask by exact Hj.
    change (Zmod.unsigned (@Zmod.zero (2 ^ RegVecSz))) with 0; rewrite Z.testbit_0_l; cbn [orb].
    destruct (Zmod.eqb_spec j i) as [-> | Hne]; [rewrite Z.eqb_refl, orb_true_r; reflexivity |].
    replace (Zmod.unsigned i =? Zmod.unsigned j) with false; [apply orb_false_r |].
    symmetry; apply Z.eqb_neq; intros He; apply Hne, Zmod.unsigned_inj; symmetry; exact He.
  Qed.

  Lemma bitOf_clr : forall j,
    bitOf (evalExpr (bitClrE type (Var type (Bit RegVecSz) w) (Var type (Bit FprIdxSz) i))) j = if Zmod.eqb j i then false else bitOf w j.
  Proof.
    intros j; pose proof (idx_range j) as Hj; unfold bitOf, bitClrE.
    cbn [evalExpr fold_left map evalNot evalAndBinary evalBinary KindCustomInd InvDefault].
    rewrite !tb_and, tb_ones32, tb_not, tb_mask by exact Hj; cbn [andb].
    destruct (Zmod.eqb_spec j i) as [-> | Hne]; [rewrite Z.eqb_refl, andb_false_r; reflexivity |].
    replace (Zmod.unsigned i =? Zmod.unsigned j) with false; [apply andb_true_r |].
    symmetry; apply Z.eqb_neq; intros He; apply Hne, Zmod.unsigned_inj; symmetry; exact He.
  Qed.
End BitVec.

Lemma bitOf_zero_eq : forall (w : bits RegVecSz) j,
  Zmod.eqb w (Zmod.of_Z (2 ^ RegVecSz) 0) = true -> bitOf w j = false.
Proof.
  intros w j H; apply Zmod.eqb_eq in H; subst w; unfold bitOf.
  change (Zmod.unsigned (Zmod.of_Z (2 ^ RegVecSz) 0)) with 0; apply Z.testbit_0_l.
Qed.

Lemma bitOf_zero : forall j, bitOf Zmod.zero j = false.
Proof. intros j; unfold bitOf; change (Zmod.unsigned (@Zmod.zero (2 ^ RegVecSz))) with 0; apply Z.testbit_0_l. Qed.
