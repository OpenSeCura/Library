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
 * `roundPack` against Flocq (`RoundCore.v`).
 *
 * For an exact real `v` located by the significand window `S` (top bit `f + 2`, weight `2^X`)
 * and a sticky bit (`inbetween_float radix2 S (X - f - 2) |v| l0`, `l0` exact iff the sticky bit
 * is clear), the integer model of `RoundBits.v` is Flocq's correctly rounded value of `v`:
 * - `rp_round`: the rounded value;
 * - `rp_ovf`: the overflow flag is Flocq's overflow condition;
 * - `rp_flags`: the three rounding flags are `Flags.roundFlags`;
 * - `rp_result`: the packed bits decode to any float with Flocq's `*_correct` description of the
 *   rounded result.
 *)

From Stdlib Require Import ZArith Zmod Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket Calc.Round IEEE754.BinarySingleNaN.
From Guru Require Import Primitives.
From Fpu Require Import FpCore.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------
 * Real helpers
 * --------------------------------------------------------------------------- *)

Lemma F2R_eq : forall m ex, F2R (Float radix2 m ex) = (IZR m * bpow radix2 ex)%R.
Proof. reflexivity. Qed.

Lemma bpow_2 : forall k, 0 <= k -> bpow radix2 k = IZR (2 ^ k).
Proof. intros k Hk; rewrite <- IZR_Zpower by exact Hk; reflexivity. Qed.

Lemma lt_scaled : forall R a b, 0 <= b - a ->
  Rlt_bool (IZR R * bpow radix2 a) (bpow radix2 b) = (R <? 2 ^ (b - a)).
Proof.
  intros R a b Hba.
  replace (bpow radix2 b) with (IZR (2 ^ (b - a)) * bpow radix2 a)%R
    by (rewrite <- bpow_2 by lia; rewrite <- bpow_plus; f_equal; lia).
  pose proof (bpow_gt_0 radix2 a) as Hp.
  destruct (Rlt_bool_spec (IZR R * bpow radix2 a) (IZR (2 ^ (b - a)) * bpow radix2 a)) as [H | H];
    destruct (Z.ltb_spec R (2 ^ (b - a))) as [H' | H']; try reflexivity.
  - apply Rmult_lt_reg_r in H; [| exact Hp]. apply lt_IZR in H. lia.
  - exfalso. apply (Rle_not_lt _ _ H). apply Rmult_lt_compat_r; [exact Hp |]. apply IZR_lt; exact H'.
Qed.

Lemma ge_scaled : forall R a k, 0 <= k -> 2 ^ k <= R -> (bpow radix2 (a + k) <= IZR R * bpow radix2 a)%R.
Proof.
  intros R a k Hk HR. rewrite bpow_plus, (Rmult_comm (bpow radix2 a)), (bpow_2 k Hk).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; exact HR].
Qed.

Lemma le_scaled : forall R a k, 0 <= k -> R <= 2 ^ k -> (IZR R * bpow radix2 a <= bpow radix2 (a + k))%R.
Proof.
  intros R a k Hk HR. rewrite bpow_plus, (Rmult_comm (bpow radix2 a)), (bpow_2 k Hk).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; exact HR].
Qed.

Lemma testbit2_odd : forall M, 0 <= M -> Z.testbit M 2 = negb (Z.even (M / 4)).
Proof.
  intros M HM. change 4 with (2 ^ 2). rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite Z.negb_even, <- Z.bit0_odd, Z.shiftr_spec by lia; reflexivity.
Qed.

Lemma cond_Ropp_abs : forall v, cond_Ropp (Rlt_bool v 0) (Rabs v) = v.
Proof. intros v; rewrite <- cond_Ropp_Rlt_bool, cond_Ropp_involutive; reflexivity. Qed.

Lemma F2R_nonneg : forall m ex, 0 <= m -> (0 <= F2R (Float radix2 m ex))%R.
Proof. intros m ex Hm; rewrite F2R_eq; apply Rmult_le_pos; [apply IZR_le; exact Hm | apply bpow_ge_0]. Qed.

(* The rounded value equals the exact one iff the location is exact. *)
Lemma exact_iff : forall s v m ex l b, Rlt_bool v 0 = s -> inbetween_float radix2 m ex (Rabs v) l -> 0 <= m ->
  (l = loc_Exact -> b = 0) -> 0 <= b <= 1 ->
  Req_bool (F2R (Float radix2 (cond_Zopp s (m + b)) ex)) v = match l with loc_Exact => true | _ => false end.
Proof.
  intros s v m ex l b Hs Hin Hm Hb Hb1.
  inversion Hin as [Hx | l' Hx Hc]; subst.
  - rewrite (Hb eq_refl), Z.add_0_r, F2R_cond_Zopp, <- Hx, cond_Ropp_abs; apply Req_bool_true; reflexivity.
  - apply Req_bool_false; intros E. apply (f_equal Rabs) in E.
    rewrite F2R_cond_Zopp, abs_cond_Ropp, Rabs_pos_eq in E by (apply F2R_nonneg; lia).
    assert (b = 0 \/ b = 1) as [-> | ->] by lia; [rewrite Z.add_0_r in E |]; lra.
Qed.

Lemma rmInc_exact : forall rmz s lsb, rmInc rmz s lsb false false = false.
Proof. intros; unfold rmInc; destruct (rneZ rmz), (rmz =? 2), (rmz =? 3), (rmz =? 4), s, lsb; reflexivity. Qed.

Lemma Bsign_B2SF : forall prec emax (b : binary_float prec emax), Bsign b = sign_SF (B2SF b).
Proof. intros prec emax [| | |]; reflexivity. Qed.

Lemma toInf_eq : forall rmz s, 0 <= rmz < 8 -> overflow_to_inf (modeZ rmz) s = rmToInf rmz s.
Proof.
  intros rmz s Hrm; destruct (rm_cases rmz Hrm) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    destruct s; reflexivity.
Qed.

Section RoundCore.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation prec := (f + 1).
  Local Abbreviation emax := (2 ^ (e - 1)).
  Local Abbreviation fexpF := (SpecFloat.fexp prec emax).

  Local Instance precGt : FLX.Prec_gt_0 prec := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax prec emax := prec_lt_emax e f Hpe.

  Lemma He2 : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Section Value.
    Variables (rmz : Z) (s : bool) (X S : Z) (st : bool) (v : R) (l0 : location).
    Hypothesis Hrm : 0 <= rmz < 8.
    Hypothesis HS : 2 ^ (f + 2) <= S < 2 ^ (f + 3).
    Hypothesis Hin : inbetween_float radix2 S (X - f - 2) (Rabs v) l0.
    Hypothesis Hl0 : l0 = loc_Exact <-> st = false.
    Hypothesis Hs : Rlt_bool v 0 = s.

    Lemma v_bounds : (bpow radix2 X <= Rabs v < bpow radix2 (X + 1))%R.
    Proof.
      pose proof (inbetween_float_bounds radix2 _ _ _ _ Hin) as [H1 H2]. rewrite F2R_eq in H1, H2. split.
      - eapply Rle_trans; [| exact H1]. replace X with ((X - f - 2) + (f + 2)) at 1 by lia. apply ge_scaled; lia.
      - eapply Rlt_le_trans; [exact H2 |]. replace (X + 1) with ((X - f - 2) + (f + 3)) by lia.
        apply le_scaled; lia.
    Qed.

    Lemma v_mag : mag radix2 v = X + 1 :> Z.
    Proof. apply mag_unique. replace (X + 1 - 1) with X by lia. exact v_bounds. Qed.

    Lemma v_cexp : cexp radix2 fexpF v = rpXEff e X - f.
    Proof.
      unfold cexp; rewrite v_mag. unfold SpecFloat.fexp, SpecFloat.emin, rpXEff, rpTiny, fpEmin, fpBias.
      destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))); lia.
    Qed.

    Lemma v_cexp_flx : cexp radix2 (FLX_exp prec) v = X - f.
    Proof. unfold cexp; rewrite v_mag; unfold FLX_exp; lia. Qed.

    (* The location after the subnormal shift and dropping the guard and round bits. *)
    Lemma v_loc : inbetween_float radix2 (rpSigS e f X S / 4) (rpXEff e X - f) (Rabs v)
                    (locOf (rpG e f X S) (rpR e f X S st)).
    Proof.
      unfold rpG, rpR, rpStS, rpSigS, rpSh, rpXEff.
      destruct (rpTiny e X) eqn:Ht.
      - unfold rpTiny in Ht; apply Z.ltb_lt in Ht.
        set (d := fpEmin e - X).
        destruct (loc_shift (Rabs v) S (X - f - 2) l0 st d ltac:(lia) Hin Hl0) as [l' [Hl'1 Hl'2]].
        assert (Eq : S / 2 ^ d = S / 2 ^ Z.min d (f + 3) /\ S mod 2 ^ d = S mod 2 ^ Z.min d (f + 3)).
        { destruct (Z.le_ge_cases d (f + 3)) as [Hd | Hd]; [rewrite Z.min_l by lia; split; reflexivity |].
          rewrite Z.min_r by lia.
          assert (2 ^ (f + 3) <= 2 ^ d) by (apply Z.pow_le_mono_r; lia).
          rewrite !Z.div_small, !Z.mod_small by lia; split; reflexivity. }
        destruct Eq as [E1 E2]; rewrite E1, E2 in *.
        replace (fpEmin e - f) with (X - f - 2 + d + 2) by (unfold d; lia).
        apply (loc_drop2 _ _ _ l'); assumption.
      - rewrite Z.pow_0_r, Z.div_1_r, Z.mod_1_r; cbn [Z.eqb negb]; rewrite orb_false_r.
        replace (X - f) with (X - f - 2 + 2) by lia.
        apply (loc_drop2 _ _ _ l0); assumption.
    Qed.

    Lemma rp_round : round radix2 fexpF (round_mode (modeZ rmz)) v =
                     F2R (Float radix2 (cond_Zopp s (rpRnd e f rmz s X S st)) (rpXEff e X - f)).
    Proof.
      rewrite (round_at fexpF rmz s v _ _ _ _ Hrm Hs v_cexp v_loc).
      unfold rpRnd, rpInc; rewrite testbit2_odd; [reflexivity |].
      pose proof (Z.pow_nonneg 2 (f + 2) ltac:(lia)).
      unfold rpSigS; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; [lia |]].
      unfold rpSh; destruct (rpTiny e X) eqn:Ht; [unfold rpTiny in Ht; apply Z.ltb_lt in Ht; lia | lia].
    Qed.

    Lemma pw : 1 <= 2 ^ (e - 1) /\ 4 <= 2 ^ f /\ 2 ^ (f + 1) = 2 * 2 ^ f /\ 2 ^ (f + 2) = 4 * 2 ^ f /\
               2 ^ (f + 3) = 8 * 2 ^ f /\ 2 ^ e = 2 * 2 ^ (e - 1).
    Proof.
      pose proof He2.
      split; [pose proof (Z.pow_le_mono_r 2 0 (e - 1)); lia |].
      split; [change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia |].
      rewrite !Z.pow_add_r by lia; change (2 ^ 1) with 2; change (2 ^ 2) with 4; change (2 ^ 3) with 8.
      split; [lia |]; split; [lia |]; split; [lia |].
      rewrite <- Z.pow_succ_r by lia; f_equal; lia.
    Qed.

    Lemma R0_range : 0 <= rpRnd e f rmz s X S st <= 2 ^ (f + 1).
    Proof. pose proof pw; apply (rnd_bound e f He2 Hf); lia. Qed.

    Lemma R0_norm : rpTiny e X = false -> 2 ^ f <= rpRnd e f rmz s X S st.
    Proof.
      intros Ht; pose proof pw as (_ & _ & _ & P2 & _).
      unfold rpRnd, rpSigS, rpSh; rewrite Ht, Z.pow_0_r, Z.div_1_r.
      assert (2 ^ f <= S / 4) by (apply Z.div_le_lower_bound; lia).
      destruct (rpInc e f rmz s X S st); cbn [b2z]; lia.
    Qed.

    Lemma abs_rv : Rabs (round radix2 fexpF (round_mode (modeZ rmz)) v) =
                   (IZR (rpRnd e f rmz s X S st) * bpow radix2 (rpXEff e X - f))%R.
    Proof.
      rewrite rp_round, F2R_cond_Zopp, abs_cond_Ropp, F2R_eq, Rabs_mult.
      rewrite (Rabs_pos_eq (IZR _)) by (apply IZR_le; apply R0_range).
      rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0; reflexivity.
    Qed.

    Lemma rp_ovf : rpOvf e f rmz s X S st =
                   negb (Rlt_bool (Rabs (round radix2 fexpF (round_mode (modeZ rmz)) v)) (bpow radix2 emax)).
    Proof.
      pose proof pw as (P1 & F4 & P1f & P2f & P3f & P2e).
      pose proof R0_range as HR.
      rewrite abs_rv. unfold rpOvf, fpEmax, fpBias.
      destruct (Z.ltb_spec (2 ^ (e - 1) - 1) X) as [Hx | Hx]; cbn [orb].
      - assert (Ht : rpTiny e X = false) by (unfold rpTiny, fpEmin, fpBias; apply Z.ltb_ge; lia).
        pose proof (R0_norm Ht) as HN.
        assert (Hxe : rpXEff e X = X) by (unfold rpXEff; rewrite Ht; reflexivity).
        rewrite Hxe, Rlt_bool_false; [reflexivity |].
        apply Rle_trans with (bpow radix2 X); [apply bpow_le; lia |].
        replace X with ((X - f) + f) at 1 by lia. apply ge_scaled; lia.
      - assert (Hxe : rpXEff e X <= 2 ^ (e - 1) - 1 /\ 2 - 2 ^ (e - 1) <= rpXEff e X)
          by (unfold rpXEff, rpTiny, fpEmin, fpBias; destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))); lia).
        rewrite lt_scaled by lia. unfold rpMagW, infMagZ, fpBias. rewrite P2e.
        set (XE := rpXEff e X) in *. set (R := rpRnd e f rmz s X S st) in *. set (P := 2 ^ (e - 1)) in *.
        destruct (Z.eq_dec XE (P - 1)) as [E0 | E0].
        + rewrite E0. replace (P - (P - 1 - f)) with (f + 1) by lia. rewrite P1f.
          destruct (Z.leb_spec ((2 * P - 1) * 2 ^ f) ((P - 1 + (P - 1) - 1) * 2 ^ f + R));
            destruct (Z.ltb_spec R (2 * 2 ^ f)); cbn; lia.
        + assert (Hp2 : 4 * 2 ^ f <= 2 ^ (P - (XE - f))) by (rewrite <- P2f; apply Z.pow_le_mono_r; lia).
          assert (Hm : (XE + (P - 1) - 1) * 2 ^ f <= (2 * P - 4) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia).
          destruct (Z.leb_spec ((2 * P - 1) * 2 ^ f) ((XE + (P - 1) - 1) * 2 ^ f + R));
            destruct (Z.ltb_spec R (2 ^ (P - (XE - f)))); cbn; lia.
    Qed.

    Lemma rp_exact : Req_bool (round radix2 fexpF (round_mode (modeZ rmz)) v) v = negb (rpInexact e f X S st).
    Proof.
      pose proof pw as (_ & F4 & _ & P2f & _).
      rewrite rp_round. unfold rpRnd, rpInexact, rpInc.
      assert (Hm : 0 <= rpSigS e f X S / 4).
      { apply Z.div_pos; [| lia]. apply (sigS_bound e f He2 Hf); lia. }
      rewrite (exact_iff s v _ _ _ _ Hs v_loc Hm).
      - destruct (rpG e f X S), (rpR e f X S st); reflexivity.
      - destruct (rpG e f X S), (rpR e f X S st); try discriminate; intros _; rewrite rmInc_exact; reflexivity.
      - destruct (rmInc _ _ _ _ _); cbn [b2z]; lia.
    Qed.

    Lemma rp_tiny : Rlt_bool (Rabs (round radix2 (FLX_exp prec) (round_mode (modeZ rmz)) v)) (bpow radix2 (2 - emax)) =
                    rpTiny e X && negb ((X =? fpEmin e - 1) && rpCarry0 f rmz s S st).
    Proof.
      pose proof pw as (P1 & F4 & P1f & P2f & P3f & P2e).
      pose proof (loc_drop2 _ _ _ _ st Hin Hl0) as Hl. replace (X - f - 2 + 2) with (X - f) in Hl by lia.
      rewrite (round_at (FLX_exp prec) rmz s v (S / 4) (X - f) _ _ Hrm Hs v_cexp_flx Hl).
      rewrite <- testbit2_odd by lia.
      assert (HQ : 2 ^ f <= S / 4 < 2 * 2 ^ f) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
      set (inc0 := rmInc rmz s (Z.testbit S 2) (Z.testbit S 1) (Z.testbit S 0 || st)).
      assert (HR1 : 2 ^ f <= S / 4 + b2z inc0 <= 2 * 2 ^ f) by (destruct inc0; cbn [b2z]; lia).
      rewrite F2R_cond_Zopp, abs_cond_Ropp, F2R_eq, Rabs_mult.
      rewrite (Rabs_pos_eq (IZR _)) by (apply IZR_le; lia).
      rewrite (Rabs_pos_eq (bpow _ _)) by apply bpow_ge_0.
      unfold rpTiny, rpCarry0, fpEmin, fpBias. fold inc0.
      destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))) as [Hx | Hx]; cbn [andb].
      - rewrite lt_scaled by lia.
        destruct (Z.eq_dec X (1 - 2 ^ (e - 1))) as [E | E].
        + replace (2 - 2 ^ (e - 1) - (X - f)) with (f + 1) by lia. rewrite P1f.
          replace (X =? 1 - (2 ^ (e - 1) - 1) - 1) with true by (symmetry; apply Z.eqb_eq; lia).
          destruct inc0; cbn [b2z andb negb];
            destruct (Z.eqb_spec (S / 4) (2 * 2 ^ f - 1)); destruct (Z.ltb_spec (S / 4 + 1) (2 * 2 ^ f));
            destruct (Z.ltb_spec (S / 4 + 0) (2 * 2 ^ f)); cbn; lia.
        + replace (X =? 1 - (2 ^ (e - 1) - 1) - 1) with false by (symmetry; apply Z.eqb_neq; lia).
          assert (4 * 2 ^ f <= 2 ^ (2 - 2 ^ (e - 1) - (X - f))) by (rewrite <- P2f; apply Z.pow_le_mono_r; lia).
          cbn [andb negb]; apply Z.ltb_lt; lia.
      - apply Rlt_bool_false.
        apply Rle_trans with (bpow radix2 X); [apply bpow_le; lia |].
        replace X with ((X - f) + f) at 1 by lia. apply ge_scaled; lia.
    Qed.

    Lemma rp_flags : roundFlags prec emax (modeZ rmz) v =
                     (rpOvf e f rmz s X S st, rpUf e f rmz s X S st, rpNx e f rmz s X S st).
    Proof.
      unfold roundFlags; cbv zeta. rewrite <- rp_ovf, rp_exact, rp_tiny.
      unfold rpUf, rpNx. destruct (rpOvf e f rmz s X S st), (rpInexact e f X S st); cbn; rewrite ?andb_false_r; reflexivity.
    Qed.

    (* Decoding a packed magnitude `A * 2^f + R` (`R` may carry into the exponent field). *)
    Lemma sf_pack : forall s' A R, 0 <= A -> 0 <= R <= 2 ^ (f + 1) -> (1 <= A -> 2 ^ f <= R) ->
      A * 2 ^ f + R < infMagZ e f ->
      let N := A * 2 ^ f + R in
      is_finite_SF (sfFields e f s' (N / 2 ^ f) (N mod 2 ^ f)) = true /\
      sign_SF (sfFields e f s' (N / 2 ^ f) (N mod 2 ^ f)) = s' /\
      SF2R radix2 (sfFields e f s' (N / 2 ^ f) (N mod 2 ^ f)) = F2R (Float radix2 (cond_Zopp s' R) (A + 2 - emax - f)).
    Proof.
      intros s' A R HA HR HAR HN N.
      pose proof pw as (P1 & F4 & P1f & P2f & P3f & P2e).
      unfold infMagZ in HN; rewrite P2e in HN.
      assert (Hbig : forall k, 2 * 2 ^ (e - 1) - 1 <= k -> (2 * 2 ^ (e - 1) - 1) * 2 ^ f <= k * 2 ^ f)
        by (intros k Hk; apply Z.mul_le_mono_nonneg_r; lia).
      unfold sfFields; rewrite P2e.
      destruct (Z_lt_le_dec R (2 ^ f)) as [H1 | H1]; [| destruct (Z.eq_dec R (2 ^ (f + 1))) as [H2 | H2]].
      - assert (A = 0) by (destruct (Z_lt_le_dec A 1); [lia | specialize (HAR l); lia]); subst A.
        unfold N; rewrite Z.mul_0_l, Z.add_0_l, Z.div_small, Z.mod_small by lia; cbn [Z.eqb].
        destruct (Z.eqb_spec R 0) as [-> | H0].
        + repeat split; destruct s'; unfold F2R; cbn; ring.
        + repeat split. cbn [SF2R]. rewrite Z2Pos.id by lia. unfold SpecFloat.emin. f_equal; f_equal; lia.
      - assert (Hd : N / 2 ^ f = A + 2) by (symmetry; apply Z.div_unique with 0; unfold N; lia).
        assert (Hm : N mod 2 ^ f = 0) by (symmetry; apply Z.mod_unique with (A + 2); unfold N; lia).
        rewrite Hd, Hm.
        assert (A + 2 < 2 * 2 ^ (e - 1) - 1) by (destruct (Z_lt_le_dec (A + 2) (2 * 2 ^ (e - 1) - 1)); [lia | specialize (Hbig _ l); lia]).
        replace (A + 2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (A + 2 =? 2 * 2 ^ (e - 1) - 1) with false by (symmetry; apply Z.eqb_neq; lia).
        repeat split. cbn [SF2R]. rewrite Z.add_0_l, Z2Pos.id by lia.
        rewrite !F2R_cond_Zopp; f_equal; rewrite !F2R_eq, H2, P1f, mult_IZR.
        replace (A + 2 + SpecFloat.emin (f + 1) (2 ^ (e - 1)) - 1) with ((A + 2 - 2 ^ (e - 1) - f) + 1)
          by (unfold SpecFloat.emin; lia).
        rewrite bpow_plus; change (bpow radix2 1) with 2%R; ring.
      - assert (Hd : N / 2 ^ f = A + 1) by (symmetry; apply Z.div_unique with (R - 2 ^ f); unfold N; lia).
        assert (Hm : N mod 2 ^ f = R - 2 ^ f) by (symmetry; apply Z.mod_unique with (A + 1); unfold N; lia).
        rewrite Hd, Hm.
        assert (A + 1 < 2 * 2 ^ (e - 1) - 1) by (destruct (Z_lt_le_dec (A + 1) (2 * 2 ^ (e - 1) - 1)); [lia | specialize (Hbig _ l); lia]).
        replace (A + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (A + 1 =? 2 * 2 ^ (e - 1) - 1) with false by (symmetry; apply Z.eqb_neq; lia).
        repeat split. cbn [SF2R]. rewrite Z.sub_add, Z2Pos.id by lia.
        unfold SpecFloat.emin; f_equal; f_equal; lia.
    Qed.

    Lemma sf_inf : forall s', sfFields e f s' (infMagZ e f / 2 ^ f) (infMagZ e f mod 2 ^ f) = S754_infinity s'.
    Proof.
      intros s'; pose proof pw as (P1 & F4 & P1f & P2f & P3f & P2e).
      unfold infMagZ, sfFields; rewrite Z.div_mul, Z.mod_mul by lia.
      replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Z.eqb_refl; reflexivity.
    Qed.

    Lemma sf_maxfin : forall s', sfFields e f s' ((infMagZ e f - 1) / 2 ^ f) ((infMagZ e f - 1) mod 2 ^ f) =
                                 S754_finite s' (Z.to_pos (2 ^ prec - 1)) (emax - prec).
    Proof.
      intros s'; pose proof pw as (P1 & F4 & P1f & P2f & P3f & P2e).
      unfold infMagZ, sfFields.
      assert (Hd : ((2 ^ e - 1) * 2 ^ f - 1) / 2 ^ f = 2 ^ e - 2)
        by (symmetry; apply Z.div_unique with (2 ^ f - 1); lia).
      assert (Hm : ((2 ^ e - 1) * 2 ^ f - 1) mod 2 ^ f = 2 ^ f - 1)
        by (symmetry; apply Z.mod_unique with (2 ^ e - 2); lia).
      rewrite Hd, Hm.
      replace (2 ^ e - 2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ e - 2 =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ f - 1 + 2 ^ f) with (2 ^ (f + 1) - 1) by lia.
      unfold SpecFloat.emin; f_equal; lia.
    Qed.

    (* The packed result is any float with Flocq's description of the rounded `v`. *)
    Lemma rp_result : forall b : binary_float prec emax,
      (if Rlt_bool (Rabs (round radix2 fexpF (round_mode (modeZ rmz)) v)) (bpow radix2 emax)
       then B2R b = round radix2 fexpF (round_mode (modeZ rmz)) v /\ is_finite b = true /\ Bsign b = s
       else B2SF b = binary_overflow prec emax (modeZ rmz) s) ->
      toB e f Hf Hpe (Zmod.of_Z _ (rpRes e f rmz s X S st)) = b.
    Proof.
      intros b Hb.
      pose proof pw as (P1 & F4 & P1f & P2f & P3f & P2e).
      pose proof R0_range as HR.
      assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; pose proof He2; lia).
      assert (Hinf : 0 < infMagZ e f < 2 ^ (f + e)) by (unfold infMagZ; rewrite Hfe, P2e; nia).
      set (A := rpXEff e X + fpBias e - 1).
      assert (HA : 0 <= A) by (unfold A, rpXEff, rpTiny, fpEmin, fpBias; destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))); lia).
      assert (HAR : 1 <= A -> 2 ^ f <= rpRnd e f rmz s X S st).
      { intros H1; apply R0_norm. unfold A, rpXEff, rpTiny, fpEmin, fpBias in H1; unfold rpTiny, fpEmin, fpBias.
        destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))); [lia | reflexivity]. }
      set (mag := rpMag e f rmz s X S st).
      assert (Hmag : 0 <= mag < 2 ^ (f + e)).
      { unfold mag, rpMag; destruct (rpOvf e f rmz s X S st) eqn:Ho; [destruct (rmToInf rmz s); lia |].
        unfold rpOvf in Ho; apply orb_false_iff in Ho as [_ Ho]; apply Z.leb_gt in Ho.
        unfold rpMagW in Ho |- *; fold A in Ho |- *.
        pose proof (Z.mul_nonneg_nonneg A (2 ^ f) HA ltac:(lia)); lia. }
      assert (HB : B2SF (toB e f Hf Hpe (Zmod.of_Z _ (rpRes e f rmz s X S st))) =
                   sfFields e f s (mag / 2 ^ f) (mag mod 2 ^ f)).
      { apply B2SF_toB_fields.
        - apply Z.mod_pos_bound; lia.
        - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        - assert (2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by (pose proof He2; lia); lia).
          rewrite tz_ofZ by (pose proof He2; unfold rpRes; fold mag; destruct s; cbn [b2z]; lia).
          unfold rpRes; fold mag. pose proof (Z.div_mod mag (2 ^ f) ltac:(lia)); lia. }
      pose proof rp_ovf as Hov.
      destruct (rpOvf e f rmz s X S st) eqn:Ho.
      - destruct (Rlt_bool _ _) in Hb, Hov; [discriminate |].
        apply B2SF_inj. rewrite HB, Hb. unfold mag, rpMag; rewrite Ho.
        unfold binary_overflow; rewrite toInf_eq by lia.
        destruct (rmToInf rmz s); [apply sf_inf | apply sf_maxfin].
      - destruct (Rlt_bool _ _) in Hb, Hov; [| discriminate].
        destruct Hb as (Hb1 & Hb2 & Hb3).
        assert (Hmw : mag = A * 2 ^ f + rpRnd e f rmz s X S st) by (unfold mag, rpMag; rewrite Ho; reflexivity).
        assert (Hlt : A * 2 ^ f + rpRnd e f rmz s X S st < infMagZ e f).
        { unfold rpOvf in Ho; apply orb_false_iff in Ho as [_ Ho]; apply Z.leb_gt in Ho; unfold rpMagW in Ho; exact Ho. }
        destruct (sf_pack s A (rpRnd e f rmz s X S st) HA HR HAR Hlt) as (S1 & S2 & S3).
        rewrite Hmw in HB.
        apply B2R_Bsign_inj.
        + rewrite <- is_finite_SF_B2SF, HB; exact S1.
        + exact Hb2.
        + rewrite <- SF2R_B2SF, HB, S3, Hb1, rp_round. unfold A, fpBias; f_equal; f_equal; lia.
        + rewrite Bsign_B2SF, HB, S2; symmetry; exact Hb3.
    Qed.
  End Value.
End RoundCore.
