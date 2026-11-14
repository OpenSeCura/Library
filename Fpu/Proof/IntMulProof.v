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
 * Correctness of the unsigned multiplier core (`IntMulProof.v`).
 *
 * Copied from `cheriot/Proof/ImplMulDivProof.v` (the parts about `mulBitStep` /
 * `mulMultiStep` only), plus `mulMultiStep_eq_Mul`, which states the result in terms of
 * Guru's `Mul` primitive.
 *)

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Fpu Require Import IntMul.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * PART 0: FOUNDATIONAL BITVECTOR (Zmod) LEMMAS
 * =========================================================================== *)

Lemma land_shiftl_small : forall x y n,
  0 <= n -> 0 <= x < 2 ^ n -> Z.land x (y * 2 ^ n) = 0.
Proof.
  intros x y n Hn Hx.
  apply Z.bits_inj_iff'; intros k Hk.
  rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_le_dec k n) as [Hlt | Hge].
  - rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r y (k - n)) by lia.
    destruct (Z.testbit x k); reflexivity.
  - assert (Hxk : Z.testbit x k = false).
    { apply Z.testbit_false; [lia |].
      replace (x / 2 ^ k) with 0; [reflexivity |].
      symmetry; apply Z.div_small; split; [lia |].
      eapply Z.lt_le_trans; [apply Hx | apply Z.pow_le_mono_r; lia]. }
    rewrite Hxk; reflexivity.
Qed.
Arguments land_shiftl_small x y [n] _ _.

Lemma lor_shiftl_small : forall x y n,
  0 <= n -> 0 <= x < 2 ^ n -> Z.lor x (Z.shiftl y n) = x + y * 2 ^ n.
Proof.
  intros x y n Hn Hx.
  rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.add_lor_land x (y * 2 ^ n)) as Hadd.
  rewrite (land_shiftl_small x y Hn Hx) in Hadd.
  lia.
Qed.
Arguments lor_shiftl_small x y [n] _ _.

Lemma lor_mul2_bit : forall q b,
  0 <= q -> 0 <= b < 2 -> Z.lor (2 * q) b = 2 * q + b.
Proof.
  intros q b Hq Hb.
  rewrite Z.lor_comm.
  replace (2 * q) with (Z.shiftl q 1) at 1 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl_small b q (n := 1)) by lia.
  change (2 ^ 1) with 2.
  lia.
Qed.

Lemma unsigned_app_arith : forall (n m : Z) (a : bits n) (b : bits m),
  0 <= n -> 0 <= m ->
  Zmod.unsigned (Zmod.app a b) = Zmod.unsigned a + Zmod.unsigned b * 2 ^ n.
Proof.
  intros n m a b Hn Hm.
  rewrite bits.unsigned_app by lia.
  apply lor_shiftl_small; [lia | apply bits.unsigned_range; lia].
Qed.

Lemma unsigned_app_zero_hi : forall (n m : Z) (a : bits n),
  0 <= n -> 0 <= m ->
  Zmod.unsigned (Zmod.app a (Zmod.zero : bits m)) = Zmod.unsigned a.
Proof.
  intros n m a Hn Hm.
  rewrite unsigned_app_arith by lia.
  rewrite Zmod.unsigned_0.
  lia.
Qed.

Unset Implicit Arguments.

Lemma unsigned_firstn : forall (n w : Z) (a : bits w),
  0 <= n ->
  Zmod.unsigned (@Zmod.firstn n w a) = Zmod.unsigned a mod 2 ^ n.
Proof.
  intros n w a Hn.
  unfold Zmod.firstn.
  rewrite Zmod.unsigned_of_Z.
  reflexivity.
Qed.

Lemma firstn_app_exact : forall (d : Z) (q r : bits d),
  0 <= d ->
  @Zmod.firstn d (d + d) (Zmod.app q r) = q.
Proof.
  intros d q r Hd.
  apply Zmod.unsigned_inj.
  rewrite unsigned_firstn by lia.
  rewrite unsigned_app_arith by lia.
  rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)); lia).
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  apply Z.mod_small; lia.
Qed.

Lemma lastn_app_exact : forall (d : Z) (q r : bits d),
  0 <= d ->
  Zmod_lastn d (Zmod.app q r) = r.
Proof.
  intros d q r Hd.
  apply Zmod.unsigned_inj.
  unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (d + d - d) with d by lia.
  rewrite unsigned_app_arith by lia.
  rewrite Z.div_add by (pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)); lia).
  pose proof (bits.unsigned_range q ltac:(lia)) as Hq.
  pose proof (bits.unsigned_range r ltac:(lia)) as Hr.
  rewrite (Z.div_small (Zmod.unsigned q) (2 ^ d)) by lia.
  rewrite Z.add_0_l.
  apply Z.mod_small; lia.
Qed.

Lemma div_pow2_step : forall (M i : Z),
  0 <= i ->
  M / 2 ^ i = 2 * (M / 2 ^ (i + 1)) + (M / 2 ^ i) mod 2.
Proof.
  intros M i Hi.
  replace (2 ^ (i + 1)) with (2 ^ i * 2) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; ring).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  apply Z_div_mod_eq_full.
Qed.

Lemma pow2_gt_lin : forall d : Z,
  0 <= d -> d < 2 ^ d.
Proof.
  intros d Hd.
  apply Z.pow_gt_lin_r; lia.
Qed.

Lemma neg1_mod_pow2 : forall w : Z,
  0 < w -> (-1) mod 2 ^ w = 2 ^ w - 1.
Proof.
  intros w Hw.
  assert (Hpos : 0 < 2 ^ w) by (apply Z.pow_pos_nonneg; lia).
  symmetry.
  apply (Zmod_unique (-1) (2 ^ w) (-1) (2 ^ w - 1)); lia.
Qed.

Lemma unsigned_and_m1_l : forall (w : Z) (x : bits w),
  0 < w ->
  Zmod.and (InvDefault (Bit w)) x = x.
Proof.
  intros w x Hw.
  apply Zmod.unsigned_inj.
  change (InvDefault (Bit w)) with (Zmod.of_Z (2 ^ w) (-1)).
  rewrite Zmod.unsigned_and, Zmod.unsigned_of_Z.
  assert (Hones : (-1) mod 2 ^ w = Z.ones w).
  { rewrite Z.ones_equiv. unfold Z.pred.
    rewrite (neg1_mod_pow2 w Hw). lia. }
  rewrite Hones.
  rewrite Z.land_comm, Z.land_ones by lia.
  pose proof (bits.unsigned_range x ltac:(lia)) as Hx.
  rewrite !(Z.mod_small (Zmod.unsigned x) (2 ^ w)) by lia.
  reflexivity.
Qed.

Lemma unsigned_extract_bit : forall (d : Z) (x : bits d) (i : nat),
  0 < d ->
  Z.of_nat i < d ->
  Zmod.unsigned (evalExpr (And [ Srl (#x) (Var type (Bit d) (bits.of_Z d (Z.of_nat i))) ; $1 ])) =
  (Zmod.unsigned x / 2 ^ (Z.of_nat i)) mod 2.
Proof.
  intros d x i Hd Hi.
  cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd].
  rewrite unsigned_and_m1_l by lia.
  rewrite Zmod.unsigned_and.
  change (Zmod.to_Z (Zmod.of_Z (2 ^ d) (Z.of_nat i))) with (Zmod.unsigned (Zmod.of_Z (2 ^ d) (Z.of_nat i))).
  rewrite Zmod.unsigned_of_Z.
  pose proof (pow2_gt_lin d ltac:(lia)) as HpowD.
  rewrite (Z.mod_small (Z.of_nat i) (2 ^ d)) by lia.
  rewrite Zmod.unsigned_sru by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Zmod.unsigned_of_Z.
  assert (H2D : 2 <= 2 ^ d).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  rewrite (Z.mod_small 1 (2 ^ d)) by lia.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 1) with 2.
  pose proof (Z.mod_pos_bound (Zmod.unsigned x / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hmod2.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

(* Option B Shift-and-Extract Lemmas *)
Lemma sll_1_iter_mod : forall {d : Z} (op1 shiftOp : bits d) (k : nat),
  0 < d ->
  Zmod.unsigned shiftOp = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
  Zmod.unsigned (evalExpr (Sll (#shiftOp) (Const type (Bit 1) (bits.of_Z 1 1)))) =
  (Zmod.unsigned op1 * 2 ^ (Z.of_nat (S k))) mod 2 ^ d.
Proof.
  intros d op1 shiftOp k Hd Hshift.
  cbn [evalExpr].
  change (Zmod.to_Z (Zmod.of_Z (2 ^ 1) 1)) with 1.
  rewrite Zmod.unsigned_slu by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2.
  rewrite Hshift.
  rewrite Z.mul_mod_idemp_l by (pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(lia)); lia).
  f_equal.
  replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
  rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.
  ring.
Qed.

Lemma unsigned_extract_msb_shifted : forall (input_width k : nat) (op1 shiftOp : bits (Z.of_nat input_width)),
  (k < input_width)%nat ->
  let d := Z.of_nat input_width in
  let i := (input_width - 1 - k)%nat in
  Zmod.unsigned shiftOp = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
  Zmod.unsigned (evalExpr (And [ Srl (#shiftOp) (Var type (Bit d) (bits.of_Z d (d - 1))) ; $1 ])) =
  (Zmod.unsigned op1 / 2 ^ (Z.of_nat i)) mod 2.
Proof.
  intros input_width k op1 shiftOp Hk d i Hshift.
  subst d i.
  replace (Z.of_nat input_width - 1) with (Z.of_nat (input_width - 1)%nat) by lia.
  rewrite (@unsigned_extract_bit (Z.of_nat input_width) shiftOp (input_width - 1)%nat ltac:(lia) ltac:(lia)).
  rewrite <- !Z.testbit_spec' by lia.
  f_equal.
  rewrite Hshift.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftl_spec by lia.
  f_equal.
  lia.
Qed.

Lemma unsigned_sub_ge : forall (w : Z) (a b : bits w),
  0 < w ->
  Zmod.unsigned b <= Zmod.unsigned a ->
  Zmod.unsigned (evalExpr (Sub (#a) (#b))) =
  Zmod.unsigned a - Zmod.unsigned b.
Proof.
  intros w a b Hw Hle.
  cbn [evalExpr Sub fold_left map evalNot KindCustomInd].
  rewrite Zmod.add_0_l.
  rewrite !Zmod.unsigned_add.
  rewrite bits.unsigned_not' by lia.
  rewrite Z.ones_equiv; unfold Z.pred.
  unfold Zmod.one; rewrite Zmod.unsigned_of_Z.
  assert (H2w : 2 <= 2 ^ w).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  rewrite (Z.mod_small 1 (2 ^ w)) by lia.
  pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
  pose proof (bits.unsigned_range b ltac:(lia)) as Hb.
  rewrite Z.add_mod_idemp_l by lia.
  transitivity (((Zmod.unsigned a - Zmod.unsigned b) + 1 * 2 ^ w) mod 2 ^ w).
  { f_equal; lia. }
  rewrite Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

Lemma slu_1_eq_mul_2 : forall (w : Z) (x : bits w),
  0 < w ->
  Zmod.slu x 1 = Zmod.mul (Zmod.of_Z (2 ^ w) 2) x.
Proof.
  intros w x Hw.
  apply Zmod.unsigned_inj.
  rewrite Zmod.unsigned_slu by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2.
  rewrite Zmod.unsigned_mul, Zmod.unsigned_of_Z.
  rewrite Z.mul_mod_idemp_l by (pose proof (Z.pow_pos_nonneg 2 w ltac:(lia) ltac:(lia)); lia).
  f_equal; ring.
Qed.


(* ===========================================================================
 * PART 1: PURE COMBINATIONAL STAGE ARITHMETIC (`Mul`, `Div`, `Shared`)
 * =========================================================================== *)

Section ParameterizedStageArithmetic.
  Variable input_width : nat.
  Hypothesis H_width_pos : (0 < input_width)%nat.

  Local Abbreviation d := (dataLen input_width).

  Lemma d_pos : 0 < d.
  Proof. unfold dataLen; lia. Qed.

  Lemma d_add_d_pos : 0 < d + d.
  Proof. pose proof d_pos; lia. Qed.

  (* --- 1A. Option B Multiplier Step Arithmetic --- *)

  Lemma mulMultiStep_add :
    forall (c1 c2 : nat) (shiftOp1 : bits d) (extOp2 mulAcc : bits (d + d)),
      evalLetExpr (@mulMultiStep input_width type (c1 + c2)%nat shiftOp1 extOp2 mulAcc) =
      let mid := evalLetExpr (@mulMultiStep input_width type c1 shiftOp1 extOp2 mulAcc) in
      evalLetExpr (@mulMultiStep input_width type c2 (mid @% "shiftOp") extOp2 (mid @% "mulAcc")).
  Proof.
    induction c1 as [| c1' IH]; intros c2 shiftOp1 extOp2 mulAcc.
    - simpl. reflexivity.
    - simpl. apply IH.
  Qed.

  Lemma mulBitStep_step :
    forall (k : nat) (op1 shiftOp1 : bits d) (extOp2 mulAcc : bits (d + d)) (c : Z),
      (k < input_width)%nat ->
      Zmod.unsigned shiftOp1 = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d ->
      mulAcc = Zmod.mul (Zmod.of_Z (2 ^ (d + d)) (c * 2 ^ (Z.of_nat k) + Zmod.unsigned op1 / 2 ^ (d - Z.of_nat k))) extOp2 ->
      let out := evalLetExpr (@mulBitStep input_width type shiftOp1 extOp2 mulAcc) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned op1 * 2 ^ (Z.of_nat (S k))) mod 2 ^ d /\
      out @% "mulAcc" =
        Zmod.mul (Zmod.of_Z (2 ^ (d + d)) (c * 2 ^ (Z.of_nat (S k)) + Zmod.unsigned op1 / 2 ^ (d - Z.of_nat (S k)))) extOp2.
  Proof.
    intros k op1 shiftOp1 extOp2 mulAcc c Hk Hshift Hacc out; unfold out; clear out.
    pose proof d_pos as Hd.
    pose proof d_add_d_pos as Hdd.
    set (i := (input_width - 1 - k)%nat).
    assert (HiZ : Z.of_nat i < d) by (unfold d, i; lia).
    assert (Hi_eq1 : d - 1 - Z.of_nat i = Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq2 : Z.of_nat i + 1 = d - Z.of_nat k) by (unfold d, i; lia).
    assert (Hi_eq3 : d - Z.of_nat i = Z.of_nat (S k)) by (unfold d, i; lia).
    assert (Hi_eq4 : Z.of_nat i = d - Z.of_nat (S k)) by (unfold d, i; lia).
    cbn [evalLetExpr mulBitStep].
    cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd].
    change (evalExpr (Const type (Bit d) (bits.of_Z d (d - 1)))) with (bits.of_Z d (d - 1)).
    split.
    - apply (sll_1_iter_mod op1 shiftOp1 k Hd Hshift).
    - set (mulBit_D := evalExpr (And [ Srl (#shiftOp1) (Var type (Bit d) (bits.of_Z d (d - 1))) ; $1 ])).
      pose proof (@unsigned_extract_msb_shifted input_width k op1 shiftOp1 Hk Hshift) as Hbit.
      fold d i mulBit_D in Hbit.
      set (b := (Zmod.unsigned op1 / 2 ^ Z.of_nat i) mod 2).
      fold b in Hbit.
      pose proof (Z.mod_pos_bound (Zmod.unsigned op1 / 2 ^ Z.of_nat i) 2 ltac:(lia)) as Hb_bound.
      fold b in Hb_bound.
      assert (H_shift1 : Zmod.to_Z (Zmod.of_Z (2 ^ 1) 1) = 1) by reflexivity.
      assert (H_accShift : evalExpr (Sll (#mulAcc) (Const type (Bit 1) (bits.of_Z 1 1))) =
                           Zmod.mul (Zmod.of_Z (2 ^ (d + d)) 2) mulAcc).
      { cbn [evalExpr]. rewrite H_shift1. apply slu_1_eq_mul_2; lia. }
      rewrite <- Hi_eq4, <- Hi_eq3.
      rewrite <- Hi_eq2, <- Hi_eq1 in Hacc.
      assert (H_top_eq : c * 2 ^ (d - Z.of_nat i) + Zmod.unsigned op1 / 2 ^ Z.of_nat i =
                         2 * (c * 2 ^ (d - 1 - Z.of_nat i) + Zmod.unsigned op1 / 2 ^ (Z.of_nat i + 1)) + b).
      { replace (d - Z.of_nat i) with ((d - 1 - Z.of_nat i) + 1) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 1) with 2.
        pose proof (div_pow2_step (Zmod.unsigned op1) (Z.of_nat i) ltac:(lia)) as Hdiv.
        fold b in Hdiv.
        lia. }
      rewrite H_top_eq, H_accShift, Hacc.
      assert (H_bit_bool : evalExpr (isNotZero (#mulBit_D)) = negb (Z.eqb b 0)).
      { cbn [evalExpr isNotZero isZero evalNot isEq KindCustomInd getDefault].
        f_equal.
        destruct (Zmod.eqb_spec mulBit_D (0%Zmod : bits d)) as [Heq | Hne].
        - rewrite Heq, Zmod.unsigned_0 in Hbit.
          symmetry; apply Z.eqb_eq; lia.
        - destruct (Z.eqb_spec b 0) as [Hb0 | Hbne]; [| reflexivity].
          exfalso; apply Hne; apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia. }
      rewrite H_bit_bool.
      set (X := c * 2 ^ (d - 1 - Z.of_nat i) + Zmod.unsigned op1 / 2 ^ (Z.of_nat i + 1)) in *.
      assert (Hb_cases : b = 0 \/ b = 1) by lia.
      destruct Hb_cases as [Hb0 | Hb1]; [rewrite Hb0 | rewrite Hb1];
        cbn [negb Z.eqb evalExpr Fst Snd snd mapDiffTuple fold_left map evalBinary KindCustomInd getDefault].
      + rewrite Z.add_0_r, Zmod.of_Z_mul, Zmod.mul_assoc. reflexivity.
      + rewrite !Zmod.add_0_l.
        apply Zmod.unsigned_inj.
        rewrite Zmod.unsigned_add, !Zmod.unsigned_mul, !Zmod.unsigned_of_Z.
        rewrite !Z.mul_mod_idemp_l, !Z.mul_mod_idemp_r, !Z.add_mod_idemp_l by lia.
        f_equal; ring.
  Qed.

  Theorem mulMultiStep_loop_invariant :
    forall (k : nat) (op1 : bits d) (extOp2 initMulAcc : bits (d + d)) (c : Z),
      (k <= input_width)%nat ->
      initMulAcc = Zmod.mul (Zmod.of_Z (2 ^ (d + d)) c) extOp2 ->
      let out := evalLetExpr (@mulMultiStep input_width type k op1 extOp2 initMulAcc) in
      Zmod.unsigned (out @% "shiftOp") = (Zmod.unsigned op1 * 2 ^ (Z.of_nat k)) mod 2 ^ d /\
      out @% "mulAcc" =
        Zmod.mul (Zmod.of_Z (2 ^ (d + d)) (c * 2 ^ (Z.of_nat k) + Zmod.unsigned op1 / 2 ^ (d - Z.of_nat k))) extOp2.
  Proof.
    induction k as [| k' IH]; intros op1 extOp2 initMulAcc c Hk Hinit out; unfold out; clear out.
    - simpl.
      cbv [readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum Fst Snd].
      change (evalExpr (Const type (Bit d) (bits.of_Z d (d - 1)))) with (bits.of_Z d (d - 1)).
      replace (Z.of_nat 0) with 0 by reflexivity.
      replace (d - 0) with d by lia.
      change (2 ^ 0) with 1.
      rewrite !Z.mul_1_r.
      pose proof d_pos as Hd.
      pose proof (bits.unsigned_range op1 ltac:(lia)) as Hop1.
      rewrite (Z.mod_small (Zmod.unsigned op1) (2 ^ d)) by lia.
      rewrite (Z.div_small (Zmod.unsigned op1) (2 ^ d)) by lia.
      rewrite Z.add_0_r.
      split; [reflexivity | exact Hinit].
    - assert (Hk' : (k' <= input_width)%nat) by lia.
      destruct (IH op1 extOp2 initMulAcc c Hk' Hinit) as [Hshift_k Hacc_k].
      replace (S k') with (k' + 1)%nat by lia.
      rewrite mulMultiStep_add.
      set (mid := evalLetExpr (@mulMultiStep input_width type k' op1 extOp2 initMulAcc)) in *.
      change (evalLetExpr (@mulMultiStep input_width type 1 (mid @% "shiftOp") extOp2 (mid @% "mulAcc")))
        with (evalLetExpr (@mulBitStep input_width type (mid @% "shiftOp") extOp2 (mid @% "mulAcc"))).
      replace (k' + 1)%nat with (S k') by lia.
      apply (mulBitStep_step k' op1 (mid @% "shiftOp") extOp2 (mid @% "mulAcc") c ltac:(lia) Hshift_k Hacc_k).
  Qed.


  Lemma unsigned_mulMultiStep_at_width :
    forall (op1 op2 : bits d),
      let extOp2 := evalExpr (ZeroExtend d (Var type (Bit d) op2)) in
      let out := evalLetExpr (@mulMultiStep input_width type input_width op1 extOp2 0%Zmod) in
      Zmod.unsigned (out @% "mulAcc") = Zmod.unsigned op1 * Zmod.unsigned op2.
  Proof.
    intros op1 op2 extOp2 out.
    pose proof d_pos as Hd.
    pose proof d_add_d_pos as Hdd.
    assert (H_init : (0%Zmod : bits (d + d)) = Zmod.mul (Zmod.of_Z (2 ^ (d + d)) 0) extOp2).
    { change (Zmod.of_Z (2 ^ (d + d)) 0) with (0%Zmod : bits (d + d)).
      rewrite Zmod.mul_0_l; reflexivity. }
    pose proof (proj2 (mulMultiStep_loop_invariant input_width op1 extOp2 0%Zmod 0 (Nat.le_refl _) H_init)) as Hmul.
    fold out in Hmul.
    change (Z.of_nat input_width) with d in Hmul.
    replace (d - d) with 0 in Hmul by lia.
    change (2 ^ 0) with 1 in Hmul.
    rewrite Z.div_1_r, Z.mul_0_l, Z.add_0_l in Hmul.
    rewrite Hmul.
    rewrite Zmod.unsigned_mul, Zmod.unsigned_of_Z.
    unfold extOp2; cbn [evalExpr ZeroExtend]; rewrite unsigned_app_arith by lia.
    rewrite Zmod.unsigned_0, Z.mul_0_l, Z.add_0_r.
    pose proof (bits.unsigned_range op1 ltac:(lia)) as Hop1.
    pose proof (bits.unsigned_range op2 ltac:(lia)) as Hop2.
    assert (H_pow2D : 2 ^ (d + d) = 2 ^ d * 2 ^ d) by (apply Z.pow_add_r; lia).
    rewrite (Z.mod_small (Zmod.unsigned op1) (2 ^ (d + d))) by nia.
    apply Z.mod_small; nia.
  Qed.

  (* The product as Guru's `Mul` on the zero-extended operands. *)
  Theorem mulMultiStep_eq_Mul :
    forall (op1 op2 : bits d),
      (evalLetExpr (@mulMultiStep input_width type input_width op1
                      (evalExpr (ZeroExtend d (Var type (Bit d) op2))) 0%Zmod)) @% "mulAcc" =
      evalExpr (Mul [ ZeroExtend d (Var type (Bit d) op1) ; ZeroExtend d (Var type (Bit d) op2) ]).
  Proof.
    intros op1 op2.
    pose proof d_pos as Hd.
    apply Zmod.unsigned_inj.
    rewrite unsigned_mulMultiStep_at_width.
    cbn [evalExpr ZeroExtend fold_left map].
    rewrite Zmod.mul_1_l.
    rewrite Zmod.unsigned_mul.
    rewrite !unsigned_app_arith by lia.
    rewrite !Zmod.unsigned_0, !Z.mul_0_l, !Z.add_0_r.
    pose proof (bits.unsigned_range op1 ltac:(lia)) as Hop1.
    pose proof (bits.unsigned_range op2 ltac:(lia)) as Hop2.
    assert (H_pow2D : 2 ^ (d + d) = 2 ^ d * 2 ^ d) by (apply Z.pow_add_r; lia).
    symmetry; apply Z.mod_small; nia.
  Qed.

End ParameterizedStageArithmetic.
