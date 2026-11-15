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
 * The aligned addition of the fused multiply-add, on integers and reals (`FmaAlign.v`).
 *
 * `align_math`: the core's `alignAdd` result `r` (window `2f + 6` bits, unit `2^(xB - 2f - 4)`)
 * and sticky bit locate the exact sum of the big and the small (shifted) operand, and the sign of
 * the sum is the sign of the big operand.
 *)

From Stdlib Require Import ZArith Reals Lia Lra Bool.
From Flocq Require Import Core.Core Calc.Bracket.
From Fpu.FlocqProof Require Import Flags.

Local Open Scope Z_scope.

Lemma bpow_IZR : forall k, 0 <= k -> bpow radix2 k = IZR (2 ^ k).
Proof. intros k Hk; rewrite <- IZR_Zpower by exact Hk; reflexivity. Qed.

(* The shifted-out fraction: `t = sm / 2^D` lies in `[q, q + 1)` with `q = sm / 2^sh`, exactly at `q`
 * iff nothing was shifted out. *)
Lemma frac_loc : forall sm sh D, 0 <= sm -> 0 <= sh <= D -> (sh = D \/ sm < 2 ^ sh) ->
  let t := (IZR sm * bpow radix2 (- D))%R in
  (IZR (sm / 2 ^ sh) <= t < IZR (sm / 2 ^ sh) + 1)%R /\ (t = IZR (sm / 2 ^ sh) <-> sm mod 2 ^ sh = 0).
Proof.
  intros sm sh D Hsm Hsh Hc t.
  assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (HpD : 2 ^ sh <= 2 ^ D) by (apply Z.pow_le_mono_r; lia).
  set (q := sm / 2 ^ sh). set (m := sm mod 2 ^ sh).
  pose proof (Z.div_mod sm (2 ^ sh) ltac:(lia)) as Hdm. fold q m in Hdm.
  pose proof (Z.mod_pos_bound sm (2 ^ sh) Hp) as Hm; fold m in Hm.
  assert (Hq : (IZR q * IZR (2 ^ sh) * bpow radix2 (- D))%R = IZR q).
  { destruct Hc as [-> | Hlt].
    - rewrite <- bpow_IZR by lia. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r. simpl; ring.
    - assert (q = 0) by (unfold q; apply Z.div_small; lia). rewrite H; simpl; ring. }
  assert (Ht : t = (IZR q + IZR m * bpow radix2 (- D))%R).
  { unfold t; rewrite Hdm, plus_IZR, mult_IZR, Rmult_plus_distr_r, (Rmult_comm (IZR (2 ^ sh)) (IZR q)), Hq. reflexivity. }
  assert (Hb : (0 <= IZR m * bpow radix2 (- D) < 1)%R).
  { split; [apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0] |].
    apply Rmult_lt_reg_r with (bpow radix2 D); [apply bpow_gt_0 |].
    rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l, Rmult_1_l, Rmult_1_r.
    simpl (bpow radix2 0). rewrite bpow_IZR by lia. apply IZR_lt; lia. }
  rewrite Ht; split; [lra |]. split.
  - intros H. assert (Hz : (IZR m * bpow radix2 (- D))%R = 0%R) by lra.
    apply Rmult_integral in Hz as [Hz | Hz]; [apply eq_IZR in Hz; exact Hz |].
    pose proof (bpow_gt_0 radix2 (- D)); lra.
  - intros H; fold m in H; rewrite H; simpl; ring.
Qed.

Section Align.
  Variable f : Z.
  Hypothesis Hf : 2 <= f.

  Local Abbreviation K := (2 * f + 4).

  Lemma align_math : forall (sB sS : bool) (xB xS big sm sh : Z),
    2 ^ (2 * f + 4) <= big < 2 ^ (2 * f + 5) -> 0 <= sm < 2 ^ (2 * f + 5) -> sm mod 8 = 0 ->
    0 <= sh <= 2 * f + 6 ->
    (sm <> 0 -> xS <= xB /\ sh = Z.min (xB - xS) (2 * f + 6)) -> (sm <> 0 -> xS = xB -> sm <= big) ->
    let st := negb (sm mod 2 ^ sh =? 0) in
    let r := if Bool.eqb sB sS then big + sm / 2 ^ sh else big - sm / 2 ^ sh - b2z st in
    let v := (cond_Ropp sB (F2R (Float radix2 big (xB - K))) + cond_Ropp sS (F2R (Float radix2 sm (xS - K))))%R in
    0 <= r < 2 ^ (2 * f + 6) /\ (st = true -> 2 ^ (2 * f + 3) <= r) /\ (Bool.eqb sB sS = true -> 0 < r) /\
    (exists l, inbetween_float radix2 r (xB - K) (Rabs v) l /\ (l = loc_Exact <-> st = false)) /\
    v = cond_Ropp sB (Rabs v).
  Proof.
    intros sB sS xB xS big sm sh Hbig Hsm H8 Hsh Hx Heq st r v.
    assert (P3 : 2 ^ (2 * f + 3) * 2 = 2 ^ (2 * f + 4)) by (replace (2 * f + 4) with (Z.succ (2 * f + 3)) by lia; rewrite Z.pow_succ_r by lia; lia).
    assert (P4 : 2 ^ (2 * f + 4) * 2 = 2 ^ (2 * f + 5)) by (replace (2 * f + 5) with (Z.succ (2 * f + 4)) by lia; rewrite Z.pow_succ_r by lia; lia).
    assert (P5 : 2 ^ (2 * f + 5) * 2 = 2 ^ (2 * f + 6)) by (replace (2 * f + 6) with (Z.succ (2 * f + 5)) by lia; rewrite Z.pow_succ_r by lia; lia).
    assert (P1 : 2 ^ (2 * f + 1) * 4 = 2 ^ (2 * f + 3)) by (replace (2 * f + 3) with ((2 * f + 1) + 2) by lia; rewrite (Z.pow_add_r 2 (2 * f + 1) 2) by lia; reflexivity).
    assert (P0 : 0 < 2 ^ (2 * f + 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
    set (u := bpow radix2 (xB - K)).
    assert (Hu : (0 < u)%R) by apply bpow_gt_0.
    destruct (Z.eq_dec sm 0) as [Hz | Hz].
    { (* nothing to add *)
      assert (Hst : st = false) by (unfold st; rewrite Hz, Z.mod_0_l by lia; reflexivity).
      assert (Hr : r = big) by (unfold r; rewrite Hst, Hz, Z.div_0_l by lia; destruct (Bool.eqb sB sS); cbn [b2z]; lia).
      assert (Hv : v = cond_Ropp sB (IZR big * u)).
      { unfold v; rewrite Hz; unfold F2R; cbn [Fnum Fexp]. rewrite Rmult_0_l; unfold u; destruct sB, sS; cbn [cond_Ropp]; ring. }
      assert (Ha : Rabs v = (IZR big * u)%R).
      { rewrite Hv, abs_cond_Ropp, Rabs_pos_eq; [reflexivity |]. apply Rmult_le_pos; [apply IZR_le; lia | lra]. }
      rewrite Hr, Hst; split; [lia |]; split; [discriminate |]; split; [lia |]; split.
      - exists loc_Exact; split; [| tauto]. constructor. rewrite Ha; reflexivity.
      - rewrite Ha; exact Hv. }
    destruct (Hx Hz) as [HxS Hsh2]. set (D := xB - xS) in *.
    pose proof (frac_loc sm sh D ltac:(lia) ltac:(lia)) as Hfr.
    assert (Hc : sh = D \/ sm < 2 ^ sh).
    { destruct (Z.le_ge_cases D (2 * f + 6)); [left; lia | right].
      rewrite Hsh2, Z.min_r by lia. lia. }
    specialize (Hfr Hc); cbv zeta in Hfr. set (q := sm / 2 ^ sh) in *. set (t := (IZR sm * bpow radix2 (- D))%R) in *.
    destruct Hfr as [Htb Hte].
    assert (Hsmv : F2R (Float radix2 sm (xS - K)) = (t * u)%R).
    { unfold F2R, t, u; cbn [Fnum Fexp]. rewrite Rmult_assoc, <- bpow_plus. f_equal; f_equal; unfold D; lia. }
    assert (Hq0 : 0 <= q) by (apply Z.div_pos; lia).
    (* integer bounds on the shifted small operand *)
    assert (Hqb : q <= big /\ (D <> 0 -> q < 2 ^ (2 * f + 4))).
    { destruct (Z.eq_dec D 0) as [HD | HD].
      - assert (sh = 0) by (rewrite Hsh2, HD; apply Z.min_l; lia). unfold q; rewrite H, Z.pow_0_r, Z.div_1_r.
        split; [apply Heq; [exact Hz | unfold D in HD; lia] | lia].
      - assert (2 <= 2 ^ sh) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
        assert (q <= sm / 2) by (apply Z.div_le_compat_l; lia).
        assert (sm / 2 < 2 ^ (2 * f + 4)) by (apply Z.div_lt_upper_bound; lia). split; [lia | intros; lia]. }
    assert (Hstq : st = true -> q < 2 ^ (2 * f + 1)).
    { intros Hs. assert (Hsh4 : 4 <= sh).
      { destruct (Z_lt_le_dec sh 4) as [Hl | Hl]; [exfalso | exact Hl].
        unfold st in Hs. apply negb_true_iff, Z.eqb_neq in Hs. apply Hs.
        assert (Hd : (2 ^ sh | sm)).
        { apply Z.divide_trans with 8; [| apply Z.mod_divide; [lia | exact H8]].
          exists (2 ^ (3 - sh)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal; lia. }
        apply Z.mod_divide; [lia | exact Hd]. }
      assert (16 <= 2 ^ sh) by (change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia).
      assert (q <= sm / 16) by (apply Z.div_le_compat_l; lia).
      assert (sm / 16 < 2 ^ (2 * f + 1)) by (apply Z.div_lt_upper_bound; lia). lia. }
    assert (HstD : st = true -> D <> 0).
    { intros Hs HD. unfold st in Hs. assert (sh = 0) by (rewrite Hsh2, HD; apply Z.min_l; lia).
      rewrite H, Z.pow_0_r, Z.mod_1_r in Hs; discriminate. }
    assert (Hst_e : t = IZR q <-> st = false).
    { rewrite Hte; unfold st. destruct (Z.eqb_spec (sm mod 2 ^ sh) 0); cbn [negb]; split; congruence. }
    destruct (Bool.eqb sB sS) eqn:Hss.
    - (* effective addition *)
      apply Bool.eqb_prop in Hss; subst sS.
      assert (Hv : v = cond_Ropp sB ((IZR big + t) * u)).
      { unfold v; rewrite Hsmv. unfold F2R at 1; cbn [Fnum Fexp]; fold u.
        destruct sB; cbn [cond_Ropp]; ring. }
      assert (Hpos : (0 <= (IZR big + t) * u)%R).
      { apply Rmult_le_pos; [| lra]. pose proof (IZR_le 0 q Hq0). pose proof (IZR_le 0 big ltac:(lia)). lra. }
      assert (Ha : Rabs v = ((IZR big + t) * u)%R) by (rewrite Hv, abs_cond_Ropp, Rabs_pos_eq by exact Hpos; reflexivity).
      split; [unfold r; lia |]. split; [intros; unfold r; lia |]. split; [intros; unfold r; lia |]. split.
      + destruct st eqn:Hs.
        * assert (Hlt : (IZR q < t)%R) by (destruct (Rle_lt_or_eq_dec _ _ (proj1 Htb)) as [Hl | Hl]; [exact Hl | apply eq_sym, Hst_e in Hl; discriminate]).
          exists (loc_Inexact (Rcompare (Rabs v) ((F2R (Float radix2 r (xB - K)) + F2R (Float radix2 (r + 1) (xB - K))) / 2))).
          split; [| split; discriminate]. apply inbetween_Inexact; [| reflexivity].
          unfold F2R; cbn [Fnum Fexp]; fold u. rewrite Ha. unfold r. rewrite !plus_IZR. split; apply Rmult_lt_compat_r; lra.
        * exists loc_Exact; split; [| tauto]. constructor. unfold F2R; cbn [Fnum Fexp]; fold u.
          rewrite Ha, (proj2 Hst_e eq_refl). unfold r; rewrite plus_IZR; reflexivity.
      + rewrite Ha; exact Hv.
    - (* effective subtraction *)
      assert (HsS : sS = negb sB) by (destruct sB, sS; cbn in Hss |- *; congruence). subst sS.
      assert (Hv : v = cond_Ropp sB ((IZR big - t) * u)).
      { unfold v; rewrite Hsmv. unfold F2R at 1; cbn [Fnum Fexp]; fold u.
        destruct sB; cbn [cond_Ropp negb]; ring. }
      destruct st eqn:Hs.
      + specialize (Hstq eq_refl). specialize (HstD eq_refl). destruct Hqb as [_ Hqb]. specialize (Hqb HstD).
        assert (Hlt : (IZR q < t)%R) by (destruct (Rle_lt_or_eq_dec _ _ (proj1 Htb)) as [Hl | Hl]; [exact Hl | apply eq_sym, Hst_e in Hl; discriminate]).
        assert (Hrv : r = big - q - 1) by (unfold r; cbn [b2z]; lia).
        assert (Hgt : (IZR q + 1 <= IZR big)%R) by (rewrite <- plus_IZR; apply IZR_le; lia).
        assert (Hpos : (0 <= (IZR big - t) * u)%R) by (apply Rmult_le_pos; lra).
        assert (Ha : Rabs v = ((IZR big - t) * u)%R) by (rewrite Hv, abs_cond_Ropp, Rabs_pos_eq by exact Hpos; reflexivity).
        split; [lia |]. split; [intros; lia |]. split; [discriminate |]. split.
        * exists (loc_Inexact (Rcompare (Rabs v) ((F2R (Float radix2 r (xB - K)) + F2R (Float radix2 (r + 1) (xB - K))) / 2))).
          split; [| split; discriminate]. apply inbetween_Inexact; [| reflexivity].
          unfold F2R; cbn [Fnum Fexp]; fold u. rewrite Ha, Hrv.
          rewrite plus_IZR, !minus_IZR. split; apply Rmult_lt_compat_r; lra.
        * rewrite Ha; exact Hv.
      + assert (Hrv : r = big - q) by (unfold r; cbn [b2z]; lia).
        assert (Htq : t = IZR q) by (apply Hst_e; reflexivity).
        assert (Hgt : (IZR q <= IZR big)%R) by (apply IZR_le; lia).
        assert (Hpos : (0 <= (IZR big - t) * u)%R) by (apply Rmult_le_pos; lra).
        assert (Ha : Rabs v = ((IZR big - t) * u)%R) by (rewrite Hv, abs_cond_Ropp, Rabs_pos_eq by exact Hpos; reflexivity).
        split; [lia |]. split; [discriminate |]. split; [discriminate |]. split.
        * exists loc_Exact; split; [| tauto]. constructor. unfold F2R; cbn [Fnum Fexp]; fold u.
          rewrite Ha, Htq, Hrv, minus_IZR; reflexivity.
        * rewrite Ha; exact Hv.
  Qed.
End Align.
