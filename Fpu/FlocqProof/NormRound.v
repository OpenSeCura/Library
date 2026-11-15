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
 * `FpCore.normRound` (reference mode) (`NormRound.v`): normalization by `clz`, then `roundPack`.
 *
 * - `clz_eval`: `clz` is `W - 1 - log2`;
 * - `normRound_eval`: for a non-zero window, `normRound` is `roundPack` on the normalized window;
 * - `norm_loc`: the location of the exact value moves to the normalized `f + 3`-bit window.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Reals.
From Flocq Require Import Core.Core Calc.Bracket.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Flags RoundBits RoundLoc.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma mod_pow2_succ : forall a n, 0 <= n ->
  a mod 2 ^ (n + 1) = a mod 2 ^ n + (if Z.testbit a n then 2 ^ n else 0).
Proof.
  intros a n Hn.
  rewrite Z.pow_add_r, Z.rem_mul_r by lia. change (2 ^ 1) with 2.
  rewrite Z.testbit_eqb by lia.
  pose proof (Z.mod_pos_bound (a / 2 ^ n) 2 ltac:(lia)).
  destruct (Z.eqb_spec ((a / 2 ^ n) mod 2) 1) as [E | E]; [rewrite E; lia |].
  replace ((a / 2 ^ n) mod 2) with 0 by lia; lia.
Qed.

Lemma bpow_2_R : forall k, 0 <= k -> bpow radix2 k = IZR (2 ^ k).
Proof. intros k Hk; rewrite <- IZR_Zpower by exact Hk; reflexivity. Qed.

Section Clz.
  Variable W m : Z.
  Variable x : bits W.
  Hypothesis HW : 0 < W.

  Local Abbreviation step := (fun (acc : Expr type (Bit m)) (i : Z) => ITE (bitSet (ty := type) x i) (cst m (W - 1 - i)) acc).

  Lemma clz_fold : forall n, (n <= Z.to_nat W)%nat ->
    evalExpr (fold_left step (map Z.of_nat (seq 0 n)) (cst m W)) =
    Zmod.of_Z _ (if Zmod.to_Z x mod 2 ^ Z.of_nat n =? 0 then W else W - 1 - Z.log2 (Zmod.to_Z x mod 2 ^ Z.of_nat n)).
  Proof.
    induction n as [| n IH]; intros Hn.
    - cbn [seq map fold_left]. rewrite Z.pow_0_r, Z.mod_1_r; reflexivity.
    - rewrite seq_S, map_app, fold_left_app; cbn [fold_left map].
      change (evalExpr (ITE (bitSet (ty := type) x (Z.of_nat (0 + n))) (cst m (W - 1 - Z.of_nat (0 + n)))
                (fold_left step (map Z.of_nat (seq 0 n)) (cst m W))) =
              Zmod.of_Z (2 ^ m) (if Zmod.to_Z x mod 2 ^ Z.of_nat (S n) =? 0 then W else W - 1 - Z.log2 (Zmod.to_Z x mod 2 ^ Z.of_nat (S n)))).
      cbn [evalExpr]. rewrite bitSet_testbit by lia. rewrite IH by lia.
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. replace (Z.of_nat (0 + n)) with (Z.of_nat n) by lia.
      rewrite mod_pow2_succ by lia.
      pose proof (Z.mod_pos_bound (Zmod.to_Z x) (2 ^ Z.of_nat n) ltac:(lia)) as Hb.
      destruct (Z.testbit (Zmod.to_Z x) (Z.of_nat n)).
      + replace (Zmod.to_Z x mod 2 ^ Z.of_nat n + 2 ^ Z.of_nat n =? 0) with false
          by (symmetry; apply Z.eqb_neq; lia).
        rewrite (Z.log2_unique _ (Z.of_nat n)) by (try lia; rewrite Z.pow_succ_r by lia; lia).
        reflexivity.
      + rewrite Z.add_0_r; reflexivity.
  Qed.

  Lemma clz_eval : 0 < Zmod.to_Z x ->
    evalExpr (clz W m x) = Zmod.of_Z _ (W - 1 - Z.log2 (Zmod.to_Z x)).
  Proof.
    intros Hx; unfold clz.
    rewrite clz_fold by lia. rewrite Z2Nat.id by lia.
    pose proof (bits.unsigned_range x ltac:(lia)).
    rewrite Z.mod_small by lia.
    replace (Zmod.to_Z x =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity.
  Qed.
End Clz.

Section Norm.
  Variable e f : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.

  Lemma normRound_eval : forall W s x wsig st rm,
    f + 4 <= W -> W < 2 ^ (e + 2) -> 0 < Zmod.to_Z wsig ->
    - 2 ^ (e + 2) <= Zmod.signed x - W ->
    let Wv := Zmod.to_Z wsig in
    let k := W - 1 - Z.log2 Wv in
    let d := W - (f + 3) in
    evalLetExpr (normRound false e f type W s x wsig st rm) =
    evalLetExpr (roundPack false e f type s (Zmod.of_Z _ (Zmod.signed x - k)) (Zmod.of_Z _ (Wv * 2 ^ k / 2 ^ d))
                   (st || negb ((Wv * 2 ^ k) mod 2 ^ d =? 0)) rm).
  Proof.
    intros W s x wsig st rm HW HW2 Hw Hx Wv k d.
    unfold normRound; cbn [evalLetExpr]. rewrite (clz_eval W (e + 3) wsig ltac:(lia) Hw).
    cbn [evalExpr]. cbn [fold_left map evalAndBinary evalOrBinary evalBinary KindCustomInd InvDefault getDefault].
    assert (Hz : evalExpr (isZero (Var type (Bit W) wsig)) = false).
    { cbn [evalExpr isZero isEq KindCustomInd getDefault].
      destruct (Zmod.eqb_spec wsig Zmod.zero) as [E | E]; [| reflexivity].
      rewrite E, Zmod.unsigned_0 in Hw; lia. }
    rewrite Hz; cbn [andb].
    change (Zmod.unsigned wsig) with Wv; fold k; fold d.
    pose proof (Z.log2_spec Wv Hw) as HL.
    pose proof (bits.unsigned_range wsig ltac:(lia)) as Hr; fold Wv in Hr.
    assert (HL2 : Z.log2 Wv < W) by (apply Z.log2_lt_pow2; lia).
    assert (Hk : 0 <= k <= W - 1) by (pose proof (Z.log2_nonneg Wv); lia).
    assert (HN : 2 ^ (W - 1) <= Wv * 2 ^ k < 2 ^ W).
    { assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). split.
      - replace (W - 1) with (Z.log2 Wv + k) by lia. rewrite Z.pow_add_r by lia. apply Z.mul_le_mono_nonneg_r; lia.
      - replace (2 ^ W) with (2 ^ Z.succ (Z.log2 Wv) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        apply Z.mul_lt_mono_pos_r; lia. }
    assert (He3 : W < 2 ^ (e + 3)) by (rewrite Z.pow_add_r by lia; change (2 ^ 3) with 8;
                                        assert (2 ^ (e + 2) = 4 * 2 ^ e) by (rewrite Z.pow_add_r by lia; lia); lia).
    assert (Hk3 : Zmod.unsigned (Zmod.of_Z (2 ^ (e + 3)) k) = k) by (apply tz_ofZ; lia).
    rewrite Hk3.
    assert (HsN : Zmod.unsigned (Zmod.slu wsig k) = Wv * 2 ^ k).
    { rewrite bits.unsigned_slu, Z.shiftl_mul_pow2 by lia; apply Z.mod_small; lia. }
    apply f_equal. f_equal.
    - rewrite (sub_eval (e + 3) ltac:(lia)); cbn [evalExpr].
      rewrite <- (Zmod.of_Z_signed x) at 1; rewrite <- Zmod.of_Z_sub; reflexivity.
    - assert (HWp : W < 2 ^ W) by (apply Z.pow_gt_lin_r; lia).
      assert (Hd2 : 2 ^ W = 2 ^ d * 2 ^ (f + 3)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hq : 0 <= Wv * 2 ^ k / 2 ^ d < 2 ^ (f + 3))
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      apply Zmod.unsigned_inj. rewrite unsigned_trunc by lia. cbn [evalExpr cst].
      rewrite (tz_ofZ W d) by lia. rewrite tz_sru by lia. rewrite HsN. rewrite (tz_ofZ (f + 3)) by lia.
      apply Z.mod_small; exact Hq.
    - cbn [evalExpr orb]. rewrite evalExpr_isNotZero_bits.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd cst].
      rewrite unsigned_and_m1_l by lia. rewrite bits.unsigned_and, HsN.
      assert (HWp : d < 2 ^ d) by (apply Z.pow_gt_lin_r; lia).
      assert (2 ^ d <= 2 ^ W) by (apply Z.pow_le_mono_r; lia).
      rewrite (tz_ofZ W (2 ^ d - 1)) by lia.
      replace (2 ^ d - 1) with (Z.ones d) by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_ones by lia; reflexivity.
  Qed.
End Norm.

Section NormLoc.
  Variable f : Z.
  Hypothesis Hf : 2 <= f.

  Lemma norm_window : forall W Wv, f + 4 <= W -> 0 < Wv < 2 ^ W ->
    let k := W - 1 - Z.log2 Wv in let d := W - (f + 3) in
    0 <= k <= W - 1 /\ 2 ^ (W - 1) <= Wv * 2 ^ k < 2 ^ W /\ 2 ^ (f + 2) <= Wv * 2 ^ k / 2 ^ d < 2 ^ (f + 3).
  Proof.
    intros W Wv HW Hw k d.
    pose proof (Z.log2_spec Wv ltac:(lia)) as HL.
    assert (HL2 : Z.log2 Wv < W) by (apply Z.log2_lt_pow2; lia).
    assert (Hk : 0 <= k <= W - 1) by (pose proof (Z.log2_nonneg Wv); lia).
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (HN : 2 ^ (W - 1) <= Wv * 2 ^ k < 2 ^ W).
    { split.
      - replace (W - 1) with (Z.log2 Wv + k) by lia. rewrite Z.pow_add_r by lia. apply Z.mul_le_mono_nonneg_r; lia.
      - replace (2 ^ W) with (2 ^ Z.succ (Z.log2 Wv) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        apply Z.mul_lt_mono_pos_r; lia. }
    split; [exact Hk |]; split; [exact HN |].
    assert (Hd1 : 2 ^ (W - 1) = 2 ^ (f + 2) * 2 ^ d) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hd2 : 2 ^ W = 2 ^ (f + 3) * 2 ^ d) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ d) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia.
  Qed.

  Lemma norm_loc : forall W Wv X st v l0, f + 4 <= W -> 0 < Wv < 2 ^ W ->
    inbetween_float radix2 Wv (X - (W - 1)) (Rabs v) l0 -> (l0 = loc_Exact <-> st = false) ->
    let k := W - 1 - Z.log2 Wv in let d := W - (f + 3) in
    (st = true -> k <= d) ->
    exists l2, inbetween_float radix2 (Wv * 2 ^ k / 2 ^ d) (X - k - f - 2) (Rabs v) l2 /\
               (l2 = loc_Exact <-> (st || negb ((Wv * 2 ^ k) mod 2 ^ d =? 0)) = false).
  Proof.
    intros W Wv X st v l0 HW Hw Hin Hl0 k d Hkd.
    destruct (norm_window W Wv HW Hw) as (Hk & HN & _); fold k d in Hk, HN.
    destruct (Z_le_gt_dec k d) as [Hle | Hgt].
    - set (j := d - k).
      assert (E1 : Wv * 2 ^ k / 2 ^ d = Wv / 2 ^ j).
      { replace d with (k + j) by (unfold j; lia). rewrite Z.pow_add_r by lia.
        rewrite (Z.mul_comm (2 ^ k) (2 ^ j)), Z.div_mul_cancel_r; [reflexivity | |]; apply Z.pow_nonzero; lia. }
      assert (E2 : (Wv * 2 ^ k) mod 2 ^ d = (Wv mod 2 ^ j) * 2 ^ k).
      { replace d with (j + k) by (unfold j; lia). rewrite Z.pow_add_r by lia.
        apply Z.mul_mod_distr_r; apply Z.pow_nonzero; lia. }
      assert (E3 : ((Wv mod 2 ^ j) * 2 ^ k =? 0) = (Wv mod 2 ^ j =? 0)).
      { assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
        destruct (Z.eqb_spec (Wv mod 2 ^ j) 0) as [-> | Hn]; [reflexivity |].
        apply Z.eqb_neq; intros H0; apply Z.mul_eq_0 in H0; lia. }
      rewrite E1, E2, E3.
      destruct (Z.eq_dec j 0) as [Hj | Hj].
      + rewrite Hj, Z.pow_0_r, Z.div_1_r, Z.mod_1_r; cbn [Z.eqb negb]; rewrite orb_false_r.
        exists l0; split; [| exact Hl0].
        replace (X - k - f - 2) with (X - (W - 1)) by (unfold j, d in Hj; lia). exact Hin.
      + destruct (loc_shift (Rabs v) Wv (X - (W - 1)) l0 st j ltac:(lia) Hin Hl0) as [l' [H1 H2]].
        exists l'; split; [| exact H2].
        replace (X - k - f - 2) with (X - (W - 1) + j) by (unfold j, d; lia). exact H1.
    - assert (Hst : st = false) by (destruct st; [specialize (Hkd eq_refl); lia | reflexivity]).
      subst st. assert (Hx : Rabs v = F2R (Float radix2 Wv (X - (W - 1)))) by (inversion Hin; [assumption | destruct Hl0 as [_ Hl1]; specialize (Hl1 eq_refl); congruence]).
      exists loc_Exact; split; [| split; [intros _ | reflexivity]].
      + constructor. rewrite Hx.
        replace (Wv * 2 ^ k / 2 ^ d) with (Wv * 2 ^ (k - d)).
        * unfold F2R; cbn [Fnum Fexp]. rewrite mult_IZR, <- bpow_2_R by lia. rewrite Rmult_assoc, <- bpow_plus. f_equal; f_equal; lia.
        * symmetry; replace k with ((k - d) + d) at 1 by lia. rewrite Z.pow_add_r, Z.mul_assoc, Z.div_mul by (try apply Z.pow_nonzero; lia). reflexivity.
      + replace k with ((k - d) + d) by lia. rewrite Z.pow_add_r, Z.mul_assoc, Z.mod_mul by (try apply Z.pow_nonzero; lia). reflexivity.
  Qed.
End NormLoc.
