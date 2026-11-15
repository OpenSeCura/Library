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
 * FCVT between formats against Flocq (`CvtFF.v`).
 *
 * `cvtFFRef e1 f1 e2 f2 rm a` (`FpCoreRef.cvtFFRef`) converts `a` from format `(e1, f1)` to format
 * `(e2, f2)`.  Flocq 4.2.2 has no `Bconv`; `cvtB` is the conversion written with Flocq:
 * `binary_normalize` (target format) of the source float's integer significand and exponent, the
 * special values unchanged.  `cvtFF_flocq_holds`: the result is `cvtB` (NaN encoded as the RISC-V
 * canonical NaN) and the flags are NV for a signaling NaN and the IEEE flags of rounding the
 * source value (`Flags.finiteFlags`) for a finite operand.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul CvtIF CvtRound.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* Variants of `NormRound.normRound_eval` / `norm_window` / `norm_loc` for windows of `f + 3` bits
 * (no bit dropped): FCVT uses the window `max (f1 + 1) (f2 + 3)`. *)
Section Norm3.
  Variable e f : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.

  (* For a normalized window (top bit set), so that no shift is needed: no bound on `W`. *)
  Lemma normRound_eval3 : forall W s x wsig st rm,
    f + 3 <= W -> 2 ^ (W - 1) <= Zmod.to_Z wsig ->
    let Wv := Zmod.to_Z wsig in
    let k := W - 1 - Z.log2 Wv in
    let d := W - (f + 3) in
    evalLetExpr (normRound false e f type W s x wsig st rm) =
    evalLetExpr (roundPack false e f type s (Zmod.of_Z _ (Zmod.signed x - k)) (Zmod.of_Z _ (Wv * 2 ^ k / 2 ^ d))
                   (st || negb ((Wv * 2 ^ k) mod 2 ^ d =? 0)) rm).
  Proof.
    intros W s x wsig st rm HW Htop Wv k d.
    assert (Hw : 0 < Zmod.to_Z wsig) by (pose proof (Z.pow_pos_nonneg 2 (W - 1) ltac:(lia) ltac:(lia)); lia).
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
    assert (Hk0 : k = 0) by (unfold k; rewrite (Z.log2_unique Wv (W - 1)); [lia | lia | rewrite Z.sub_1_r, Z.succ_pred; lia]).
    assert (Hk3 : Zmod.unsigned (Zmod.of_Z (2 ^ (e + 3)) k) = k)
      by (apply tz_ofZ; [lia | rewrite Hk0; pose proof (Z.pow_pos_nonneg 2 (e + 3) ltac:(lia) ltac:(lia)); lia]).
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
End Norm3.

Section NormLoc3.
  Variable f : Z.
  Hypothesis Hf : 2 <= f.

  Lemma norm_window3 : forall W Wv, f + 3 <= W -> 0 < Wv < 2 ^ W ->
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

  Lemma norm_loc3 : forall W Wv X st v l0, f + 3 <= W -> 0 < Wv < 2 ^ W ->
    inbetween_float radix2 Wv (X - (W - 1)) (Rabs v) l0 -> (l0 = loc_Exact <-> st = false) ->
    let k := W - 1 - Z.log2 Wv in let d := W - (f + 3) in
    (st = true -> k <= d) ->
    exists l2, inbetween_float radix2 (Wv * 2 ^ k / 2 ^ d) (X - k - f - 2) (Rabs v) l2 /\
               (l2 = loc_Exact <-> (st || negb ((Wv * 2 ^ k) mod 2 ^ d =? 0)) = false).
  Proof.
    intros W Wv X st v l0 HW Hw Hin Hl0 k d Hkd.
    destruct (norm_window3 W Wv HW Hw) as (Hk & HN & _); fold k d in Hk, HN.
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
End NormLoc3.

Lemma land_pow2_small : forall c n, 0 <= n -> 0 <= c < 2 ^ n -> Z.land c (2 ^ n) = 0.
Proof.
  intros c n Hn Hc. apply Z.bits_inj'; intros i Hi.
  rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
  destruct (Z.eqb_spec n i) as [<- | _]; [| apply andb_false_r].
  rewrite <- (Z.mod_small c (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* Flipping bit `n` of the two's complement `X` (in `n + 1` bits) adds `2^n`. *)
Lemma xor_flip : forall X n, 0 <= n -> - 2 ^ n <= X < 2 ^ n -> Z.lxor (X mod 2 ^ (n + 1)) (2 ^ n) = X + 2 ^ n.
Proof.
  intros X n Hn HX.
  assert (HP : 2 ^ (n + 1) = 2 * 2 ^ n) by (rewrite Z.pow_add_r by lia; lia).
  destruct (Z_lt_le_dec X 0) as [Hneg | Hpos].
  - rewrite <- (Z.mod_unique X (2 ^ (n + 1)) (-1) (X + 2 ^ (n + 1))) by lia.
    set (c := X + 2 ^ n).
    replace (X + 2 ^ (n + 1)) with (Z.lxor c (2 ^ n))
      by (rewrite <- Z.add_nocarry_lxor by (apply land_pow2_small; unfold c; lia); unfold c; lia).
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
  - rewrite Z.mod_small by lia. rewrite <- Z.add_nocarry_lxor by (apply land_pow2_small; lia). reflexivity.
Qed.

Lemma mkOut_snd : forall e f (r : Expr type (FpBits e f)) (fl : Expr type (Bit 5)),
  (evalExpr (mkOut e f type r fl)).(Snd).(Fst) = evalExpr fl.
Proof. reflexivity. Qed.

(* Clamping the exponent below `emin - (f + 4)` or above `emax + 1` does not change rounding. *)
Section Clamp.
  Variables e f : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.

  Definition clampZ (X : Z) : Z :=
    if X <? fpEmin e - (f + 4) then fpEmin e - (f + 4) else if fpEmax e + 1 <? X then fpEmax e + 1 else X.

  Lemma rp_clamp : forall rmz s X S st,
    rpRes e f rmz s (clampZ X) S st = rpRes e f rmz s X S st /\
    rpOvf e f rmz s (clampZ X) S st = rpOvf e f rmz s X S st /\
    rpUf e f rmz s (clampZ X) S st = rpUf e f rmz s X S st /\
    rpNx e f rmz s (clampZ X) S st = rpNx e f rmz s X S st.
  Proof.
    intros rmz s X S st. unfold clampZ.
    assert (Hp : 1 <= 2 ^ (e - 1)) by (pose proof (Z.pow_le_mono_r 2 0 (e - 1)); lia).
    unfold fpEmin, fpEmax, fpBias.
    destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1) - (f + 4))) as [Hlo | Hlo];
      [| destruct (Z.ltb_spec (2 ^ (e - 1) - 1 + 1) X) as [Hhi | Hhi]]; [| | repeat split; reflexivity].
    - set (L := 1 - (2 ^ (e - 1) - 1) - (f + 4)) in *.
      assert (T1 : rpTiny e L = rpTiny e X) by (unfold rpTiny, fpEmin, fpBias; rewrite !(proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      assert (T0 : rpTiny e X = true) by (unfold rpTiny, fpEmin, fpBias; apply Z.ltb_lt; lia).
      assert (T2 : rpSh e f L = rpSh e f X) by (unfold rpSh; rewrite T1, T0; unfold fpEmin, fpBias; lia).
      assert (T3 : rpXEff e L = rpXEff e X) by (unfold rpXEff; rewrite T1, T0; reflexivity).
      assert (T4 : (fpEmax e <? L) = (fpEmax e <? X)) by (unfold fpEmax, fpBias; rewrite !(proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      assert (T5 : (L =? fpEmin e - 1) = (X =? fpEmin e - 1)) by (unfold fpEmin, fpBias; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
      unfold rpRes, rpUf, rpNx, rpInexact, rpMag, rpOvf, rpMagW, rpRnd, rpInc, rpG, rpR, rpStS, rpSigS.
      rewrite T1, T2, T3, T4, T5. repeat split; reflexivity.
    - set (H := 2 ^ (e - 1) - 1 + 1) in *.
      assert (O1 : rpOvf e f rmz s H S st = true) by (unfold rpOvf, fpEmax, fpBias; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      assert (O2 : rpOvf e f rmz s X S st = true) by (unfold rpOvf, fpEmax, fpBias; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      assert (T1 : rpTiny e H = false) by (unfold rpTiny, fpEmin, fpBias; apply Z.ltb_ge; lia).
      assert (T2 : rpTiny e X = false) by (unfold rpTiny, fpEmin, fpBias; apply Z.ltb_ge; lia).
      unfold rpRes, rpMag, rpUf, rpNx. rewrite O1, O2, T1, T2, !orb_true_r. repeat split; reflexivity.
  Qed.
End Clamp.

Section CvtFF.
  Variables e1 f1 e2 f2 : Z.
  Hypothesis Hf1 : 2 <= f1.
  Hypothesis Hpe1 : f1 + 1 < 2 ^ (e1 - 1).
  Hypothesis Hf2 : 2 <= f2.
  Hypothesis Hpe2 : f2 + 1 < 2 ^ (e2 - 1).

  Local Abbreviation ew := (Z.max e1 e2 + 3).
  Local Abbreviation ww := (Z.max (f1 + 1) (f2 + 3)).

  Local Abbreviation uSign := (fun (u : type (FpUnpK e1 f1)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e1 f1)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e1 f1)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e1 f1)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e1 f1)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e1 f1)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e1 f1)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  (* `cvtFF false` on an unpacked operand, transcribed. *)
  Definition cvtV (rm : bits 3) (a : bits (f1 + e1 + 1)) (ua : type (FpUnpK e1 f1)) : type (FpOutK e2 f2) :=
    let s := uSign ua in
    let x1 := evalExpr (Add [ zext (e1 + 3) ew (Xor [ Var type (Bit (e1 + 3)) (uExp ua) ; cst (e1 + 3) (2 ^ (e1 + 2)) ]) ;
                              cst ew (expOff false e2 - expOff false e1 - 2 ^ (e1 + 2)) ]) in
    let lo := evalExpr (@cst type ew (fpEmin e2 - (f2 + 4) + expOff false e2)) in
    let hi := evalExpr (@cst type ew (fpEmax e2 + 1 + expOff false e2)) in
    let below := evalExpr (Slt (Var type (Bit ew) x1) (Var type (Bit ew) lo)) in
    let above := evalExpr (Slt (Var type (Bit ew) hi) (Var type (Bit ew) x1)) in
    let xc := evalExpr (ITE (Var type Bool below) (Var type (Bit ew) lo) (ITE (Var type Bool above) (Var type (Bit ew) hi) (Var type (Bit ew) x1))) in
    let x2 := evalExpr (trunc ew (e2 + 3) (Var type (Bit ew) xc)) in
    let wsig := evalExpr (Sll (zext (f1 + 1) ww (Var type (Bit (f1 + 1)) (uSig ua))) (cst ww (ww - (f1 + 1)))) in
    if uNaN ua then evalExpr (mkOut e2 f2 type (qnanE e2 f2 type)
                      (mkFlags type (ConstBool (uSNaN ua)) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
    else if uInf ua then evalExpr (mkOut e2 f2 type (infE e2 f2 type (ConstBool s)) (noFlags type))
    else if uZero ua then evalExpr (mkOut e2 f2 type (zeroE e2 f2 type (ConstBool s)) (noFlags type))
    else evalLetExpr (normRound false e2 f2 type ww s x2 wsig false rm).

  Lemma cvtFF_V : forall rm a,
    evalLetExpr (cvtFFRef e1 f1 e2 f2 type rm a) = cvtV rm a (evalLetExpr (fpUnpack false e1 f1 type a)).
  Proof. intros; exact eq_refl. Qed.
  Local Abbreviation toB1 := (toB e1 f1 Hf1 Hpe1).
  Local Abbreviation ofB2 := (ofB e2 f2 Hf2).
  Local Abbreviation unp1 := (fun x => evalLetExpr (fpUnpack false e1 f1 type x)).

  Local Instance precGt2 : FLX.Prec_gt_0 (f2 + 1) := prec_gt_0 e2 f2 Hf2.
  Local Instance precLt2 : Prec_lt_emax (f2 + 1) (2 ^ (e2 - 1)) := prec_lt_emax e2 f2 Hpe2.


  (* Format conversion in Flocq (4.2.2 has no `Bconv`): `binary_normalize` of the source float. *)
  Definition cvtB (m : mode) (x : BinarySingleNaN.binary_float (f1 + 1) (2 ^ (e1 - 1))) :
      BinarySingleNaN.binary_float (f2 + 1) (2 ^ (e2 - 1)) :=
    match x with
    | BinarySingleNaN.B754_nan => BinarySingleNaN.B754_nan
    | BinarySingleNaN.B754_zero s => BinarySingleNaN.B754_zero s
    | BinarySingleNaN.B754_infinity s => BinarySingleNaN.B754_infinity s
    | BinarySingleNaN.B754_finite s mx ex _ =>
        BinarySingleNaN.binary_normalize (f2 + 1) (2 ^ (e2 - 1)) precGt2 precLt2 m (cond_Zopp s (Zpos mx)) ex s
    end.

  Definition cvtFlags (rm : bits 3) (a : bits (f1 + e1 + 1)) : bits 5 :=
    match toB1 a with
    | BinarySingleNaN.B754_nan => mkFl (isSNaN e1 f1 Hf1 Hpe1 a) false false false false
    | BinarySingleNaN.B754_finite _ _ _ _ => finiteFlags (f2 + 1) (2 ^ (e2 - 1)) (modeOf rm) (BinarySingleNaN.B2R (toB1 a))
    | _ => mkFl false false false false false
    end.

  Definition cvtFF_flocq : Prop :=
    forall rm a,
      (evalLetExpr (cvtFFRef e1 f1 e2 f2 type rm a)) @% "res" = ofB2 (cvtB (modeOf rm) (toB1 a)) /\
      (evalLetExpr (cvtFFRef e1 f1 e2 f2 type rm a)) @% "flags" = cvtFlags rm a.

  Lemma He1C : 2 <= e1.
  Proof. exact (He e1 f1 Hf1 Hpe1). Qed.

  Lemma He2C : 2 <= e2.
  Proof. exact (He e2 f2 Hf2 Hpe2). Qed.

  Lemma cvt_main : forall rm a s E M,
    0 <= M < 2 ^ f1 -> 0 <= E < 2 ^ e1 -> Zmod.to_Z a = b2z s * 2 ^ (f1 + e1) + E * 2 ^ f1 + M ->
    E <> 2 ^ e1 - 1 -> (E <> 0 \/ M <> 0) ->
    (cvtV rm a (unp1 a)).(Fst) = ofB2 (cvtB (modeOf rm) (toB1 a)) /\
    (cvtV rm a (unp1 a)).(Snd).(Fst) = finiteFlags (f2 + 1) (2 ^ (e2 - 1)) (modeOf rm) (BinarySingleNaN.B2R (toB1 a)).
  Proof.
    intros rm a s E M HM HE Ha Hn Hz.
    pose proof He1C as He1. pose proof He2C as He2.
    pose proof (fin_facts e1 f1 Hf1 Hpe1 a s E M HM HE Ha Hn Hz) as FF; cbv beta zeta in FF.
    destruct FF as (HSg & HX & HV & Hfin & Hsgn).
    pose proof (u_nan e1 f1 He1 Hf1 a s E M HM HE Ha) as Hun. pose proof (u_inf e1 f1 He1 Hf1 a s E M HM HE Ha) as Hui.
    pose proof (u_zero e1 f1 He1 Hf1 a s E M HM HE Ha) as Huz. pose proof (u_sign e1 f1 He1 Hf1 a s E M HM HE Ha) as Hus.
    replace ((E =? 2 ^ e1 - 1) && negb (M =? 0)) with false in Hun by (destruct (Z.eqb_spec E (2 ^ e1 - 1)); [lia | reflexivity]).
    replace ((E =? 2 ^ e1 - 1) && (M =? 0)) with false in Hui by (destruct (Z.eqb_spec E (2 ^ e1 - 1)); [lia | reflexivity]).
    replace ((E =? 0) && (M =? 0)) with false in Huz by (destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); try reflexivity; lia).
    pose proof (cls e1 f1 Hf1 Hpe1 a s E M HM HE Ha) as C.
    destruct (toB1 a) as [s' | s' | | s' mx ex Hb'] eqn:Hb; cbn [clsP] in C; try lia.
    destruct C as (-> & _). cbn [cvtB].
    set (v := BinarySingleNaN.B2R (BinarySingleNaN.B754_finite s mx ex Hb')) in *.
    set (ua := unp1 a) in *. clearbody ua.
    destruct ua as [s0 [z0 [i0 [n0 [sn0 [xv [sig []]]]]]]]; cbn [Fst Snd] in *. subst s0 z0 i0 n0.
    set (X := Zmod.signed xv) in *. set (Sg := Zmod.to_Z sig) in *.
    assert (HXd : Zmod.signed xv = X) by reflexivity. assert (HSd : Zmod.to_Z sig = Sg) by reflexivity.
    clearbody X Sg.
    unfold fpEmin, fpEmax, fpBias in HX.
    unfold cvtV; cbv zeta; cbn [Fst Snd]. cbv iota.
    change (expOff false e1) with 0. change (expOff false e2) with 0.
    (* powers *)
    assert (Pe1 : 2 ^ (e1 + 2) = 8 * 2 ^ (e1 - 1)) by (replace (e1 + 2) with ((e1 - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Pe2 : 2 ^ (e2 + 2) = 8 * 2 ^ (e2 - 1)) by (replace (e2 + 2) with ((e2 - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Pe2' : 2 ^ (e2 + 1) = 4 * 2 ^ (e2 - 1)) by (replace (e2 + 1) with ((e2 - 1) + 2) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Pe13 : 2 ^ (e1 + 3) = 2 * 2 ^ (e1 + 2)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Pew1 : 2 ^ (e1 + 2) <= 2 ^ (ew - 1)) by (apply Z.pow_le_mono_r; lia).
    assert (Pew2 : 2 ^ (e2 + 2) <= 2 ^ (ew - 1)) by (apply Z.pow_le_mono_r; lia).
    assert (Pew : 2 ^ ew = 2 * 2 ^ (ew - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Pf1 : 2 ^ (f1 + 1) = 2 * 2 ^ f1) by (rewrite Z.pow_add_r by lia; lia).
    (* the exponent, sign-extended *)
    match goal with |- context [evalExpr (Add [zext ?i ?o ?t; ?c])] => set (x1 := evalExpr (Add [zext i o t; c])) end.
    assert (Hx1 : x1 = Zmod.of_Z (2 ^ ew) X).
    { apply Zmod.unsigned_inj. unfold x1. cbn [evalExpr fold_left map]. rewrite !Zmod.unsigned_add, Zmod.unsigned_0, Z.add_0_l.
      rewrite unsigned_zext by lia. cbn [evalExpr fold_left map evalXorBinary evalBinary KindCustomInd getDefault cst].
      rewrite !bits.unsigned_xor, Zmod.unsigned_0, Z.lxor_0_l, (tz_ofZ (e1 + 3) (2 ^ (e1 + 2))) by lia.
      rewrite <- (Zmod.of_Z_signed xv), HXd, Zmod.unsigned_of_Z. replace (e1 + 3) with ((e1 + 2) + 1) by lia.
      assert (HXr : - 2 ^ (e1 + 2) <= X < 2 ^ (e1 + 2)) by lia. rewrite xor_flip by lia. rewrite Zmod.unsigned_of_Z, Zmod.unsigned_of_Z, Z.add_mod_idemp_r, Z.add_mod_idemp_l by lia. f_equal; lia. }
    clearbody x1.
    change (evalExpr (@cst type ew (fpEmin e2 - (f2 + 4) + 0))) with (Zmod.of_Z (2 ^ ew) (fpEmin e2 - (f2 + 4) + 0)).
    change (evalExpr (@cst type ew (fpEmax e2 + 1 + 0))) with (Zmod.of_Z (2 ^ ew) (fpEmax e2 + 1 + 0)).
    match goal with |- context [evalExpr (trunc ?i ?o ?t)] => set (x2 := evalExpr (trunc i o t)) end.
    assert (Hx2 : x2 = Zmod.of_Z (2 ^ (e2 + 3)) (clampZ e2 f2 X)).
    { apply Zmod.unsigned_inj. unfold x2. rewrite unsigned_trunc by lia. cbn [evalExpr]. rewrite !(slt_eval ew) by lia.
      cbn [evalExpr]. rewrite Hx1.
      unfold fpEmin, fpEmax, fpBias in *. rewrite !Z.add_0_r.
      rewrite !(signed_of_Z_small ew) by lia.
      unfold clampZ, fpEmin, fpEmax, fpBias.
      destruct (X <? 1 - (2 ^ (e2 - 1) - 1) - (f2 + 4)), (2 ^ (e2 - 1) - 1 + 1 <? X);
        rewrite !Zmod.unsigned_of_Z, mod_pow2_mod by lia; reflexivity. }
    clearbody x2. subst x2.
    clear Hx1 x1. try clear Ha. try clear HM. try clear HE. try clear Hn. try clear Hz. try clear HXd. try clear Pe13. try clear Pew1. try clear Pew2. try clear Pew. try clear Hfin.
    match goal with |- context [evalExpr (Sll ?a ?b)] => set (wsig := evalExpr (Sll a b)) end.
    assert (HP0 : 2 ^ (ww - (f1 + 1)) * 2 ^ (f1 + 1) = 2 ^ ww) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hw0 : 0 < 2 ^ (ww - (f1 + 1))) by (apply Z.pow_pos_nonneg; lia).
    set (Wv := Sg * 2 ^ (ww - (f1 + 1))).
    assert (HWv : 2 ^ (ww - 1) <= Wv < 2 ^ ww).
    { unfold Wv. replace (2 ^ (ww - 1)) with (2 ^ f1 * 2 ^ (ww - (f1 + 1))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      split; [apply Z.mul_le_mono_nonneg_r; lia |]. rewrite <- HP0, Z.mul_comm. apply Z.mul_lt_mono_pos_l; lia. }
    assert (Hwsig : Zmod.to_Z wsig = Wv).
    { unfold wsig. cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr cst].
      assert (ww - (f1 + 1) < 2 ^ ww) by (pose proof (Z.pow_gt_lin_r 2 ww ltac:(lia) ltac:(lia)); lia).
      rewrite (tz_ofZ ww (ww - (f1 + 1))) by lia. rewrite HSd, Z.shiftl_mul_pow2 by lia. apply Z.mod_small; lia. }
    clearbody wsig.
    assert (Hcl : 1 - (2 ^ (e2 - 1) - 1) - (f2 + 4) <= clampZ e2 f2 X <= 2 ^ (e2 - 1) - 1 + 1)
      by (unfold clampZ, fpEmin, fpEmax, fpBias; destruct (Z.ltb_spec X (1 - (2 ^ (e2 - 1) - 1) - (f2 + 4))); [lia |];
          destruct (Z.ltb_spec (2 ^ (e2 - 1) - 1 + 1) X); lia).
    assert (Hx2s : Zmod.signed (Zmod.of_Z (2 ^ (e2 + 3)) (clampZ e2 f2 X)) = clampZ e2 f2 X) by (apply signed_k; lia).
    pose proof (normRound_eval3 e2 f2 He2 Hf2 ww s (Zmod.of_Z _ (clampZ e2 f2 X)) wsig false rm ltac:(lia)
                  ltac:(rewrite Hwsig; lia)) as HR.
    cbv zeta in HR; rewrite HR; clear HR.
    rewrite (roundPack_Z e2 f2 He2 Hf2 Hpe2). cbn [Fst Snd]. rewrite Hx2s, Hwsig.
    assert (Hk0 : ww - 1 - Z.log2 Wv = 0) by (rewrite (Z.log2_unique Wv (ww - 1)); [lia | lia | rewrite Z.sub_1_r, Z.succ_pred; lia]).
    rewrite Hk0, Z.pow_0_r, Z.mul_1_r, Z.sub_0_r.
    set (d := ww - (f2 + 3)).
    destruct (norm_window3 f2 Hf2 ww Wv ltac:(lia) ltac:(lia)) as (_ & _ & HSw); rewrite Hk0, Z.pow_0_r, Z.mul_1_r in HSw; fold d in HSw.
    rewrite signed_k, tz_ofZ by lia.
    destruct (rp_clamp e2 f2 He2 Hf2 (Zmod.to_Z rm) s X (Wv / 2 ^ d) (false || negb (Wv mod 2 ^ d =? 0))) as (R1 & R2 & R3 & R4).
    rewrite R1, R2, R3, R4.
    (* the real side *)
    assert (Hpos : (0 < F2R (Float radix2 Sg (X - f1)))%R) by (apply F2R_gt_0; cbn; lia).
    assert (Hs : Rlt_bool v 0 = s) by (rewrite HV; apply Rlt_bool_cond_Ropp; exact Hpos).
    assert (Hin : inbetween_float radix2 Wv (X - (ww - 1)) (Rabs v) loc_Exact).
    { constructor. rewrite HV, abs_cond_Ropp, Rabs_pos_eq by lra. unfold Wv.
      replace (X - (ww - 1)) with ((X - f1) - (ww - (f1 + 1))) by lia. rewrite F2R_scale by lia. reflexivity. }
    destruct (norm_loc3 f2 Hf2 ww Wv X false v loc_Exact ltac:(lia) ltac:(lia) Hin ltac:(split; reflexivity) ltac:(discriminate))
      as (l2 & Hin2 & Hl2).
    rewrite Hk0, Z.pow_0_r, Z.mul_1_r, Z.sub_0_r in Hin2. rewrite Hk0, Z.pow_0_r, Z.mul_1_r in Hl2. fold d in Hin2, Hl2.
    assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)); change (2 ^ 3) with 8 in *; lia).
    pose proof (BinarySingleNaN.binary_normalize_correct (f2 + 1) (2 ^ (e2 - 1)) precGt2 precLt2 (modeOf rm) (cond_Zopp s (Zpos mx)) ex s) as HN0.
    cbv zeta in HN0.
    change (F2R (Float radix2 (cond_Zopp s (Z.pos mx)) ex)) with v in HN0.
    rewrite Hs in HN0.
    replace (match Rcompare v 0 with Datatypes.Eq => s | Lt => true | Gt => false end) with s in HN0
      by (rewrite HV; destruct s; cbn [cond_Ropp]; [rewrite Rcompare_Lt by lra | rewrite Rcompare_Gt by lra]; reflexivity).
    split.
    - set (bn := BinarySingleNaN.binary_normalize (f2 + 1) (2 ^ (e2 - 1)) precGt2 precLt2 (modeOf rm) (cond_Zopp s (Z.pos mx)) ex s) in *.
      assert (Hbn : toB e2 f2 Hf2 Hpe2 (Zmod.of_Z _ (rpRes e2 f2 (Zmod.to_Z rm) s X (Wv / 2 ^ d) (false || negb (Wv mod 2 ^ d =? 0)))) = bn).
      { apply (rp_result e2 f2 Hf2 Hpe2 _ _ _ _ _ v l2 Hrm HSw Hin2 Hl2 Hs). exact HN0. }
      rewrite <- Hbn, ofB_toB; [reflexivity |]. rewrite Hbn.
      destruct (Rlt_bool _ _) in HN0.
      + destruct HN0 as (_ & Hfin' & _). destruct bn; try reflexivity; discriminate Hfin'.
      + exact (B2SF_overflow_nan e2 f2 _ _ _ HN0).
    - unfold finiteFlags. change (modeOf rm) with (modeZ (Zmod.to_Z rm)).
      rewrite (rp_flags e2 f2 Hf2 Hpe2 _ _ _ _ _ v l2 Hrm HSw Hin2 Hl2 Hs). reflexivity.
  Qed.

  Lemma cvt_res : forall rm a, (evalLetExpr (cvtFFRef e1 f1 e2 f2 type rm a)) @% "res" = (cvtV rm a (unp1 a)).(Fst).
  Proof. intros; rewrite cvtFF_V; reflexivity. Qed.

  Lemma cvt_flags : forall rm a, (evalLetExpr (cvtFFRef e1 f1 e2 f2 type rm a)) @% "flags" = (cvtV rm a (unp1 a)).(Snd).(Fst).
  Proof. intros; rewrite cvtFF_V; reflexivity. Qed.

  Theorem cvtFF_flocq_holds : cvtFF_flocq.
  Proof.
    intros rm a. rewrite cvt_res, cvt_flags.
    pose proof He1C as He1.
    destruct (split_fields e1 f1 Hf1 Hpe1 a) as (s & E & M & HM & HE & Ha).
    pose proof (cls e1 f1 Hf1 Hpe1 a s E M HM HE Ha) as C.
    pose proof (u_nan e1 f1 He1 Hf1 a s E M HM HE Ha) as Hun. pose proof (u_inf e1 f1 He1 Hf1 a s E M HM HE Ha) as Hui.
    pose proof (u_zero e1 f1 He1 Hf1 a s E M HM HE Ha) as Huz. pose proof (u_snan e1 f1 He1 Hf1 a s E M HM HE Ha) as Hus.
    pose proof (u_sign e1 f1 He1 Hf1 a s E M HM HE Ha) as Hsg.
    pose proof (isSNaN_eq e1 f1 Hf1 Hpe1 a s E M HM HE Ha) as Hsn.
    assert (He4 : 4 <= 2 ^ e1) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    destruct (Z.eq_dec E (2 ^ e1 - 1)) as [HE1 | HE1]; [destruct (Z.eq_dec M 0) as [HM0 | HM0] |].
    - (* infinity *)
      rewrite HE1, HM0, Z.eqb_refl in Hun, Hui. cbn [andb negb] in Hun, Hui.
      unfold cvtV, cvtFlags; cbv zeta. rewrite Hun, Hui, Hsg. cbv iota.
      destruct (toB1 a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
      destruct C as (-> & _). cbn [cvtB]. rewrite (ofB_inf e2 f2 Hf2 Hpe2). split; reflexivity.
    - (* NaN *)
      rewrite HE1, Z.eqb_refl in Hun, Hus, Hsn. replace (M =? 0) with false in Hun, Hus, Hsn by (symmetry; apply Z.eqb_neq; exact HM0).
      cbn [andb negb] in Hun, Hus, Hsn.
      unfold cvtV, cvtFlags; cbv zeta. rewrite Hun. cbv iota.
      destruct (toB1 a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
      cbn [cvtB]. rewrite (ofB_nan e2 f2 Hf2 Hpe2). split; [reflexivity |].
      rewrite mkOut_snd, mkFlags_eval, Hus, Hsn. reflexivity.
    - replace ((E =? 2 ^ e1 - 1) && negb (M =? 0)) with false in Hun by (destruct (Z.eqb_spec E (2 ^ e1 - 1)); [lia | reflexivity]).
      replace ((E =? 2 ^ e1 - 1) && (M =? 0)) with false in Hui by (destruct (Z.eqb_spec E (2 ^ e1 - 1)); [lia | reflexivity]).
      assert (Hzd : (E = 0 /\ M = 0) \/ (E <> 0 \/ M <> 0)) by lia.
      destruct Hzd as [[HE0 HM0] | Hz].
      + (* zero *)
        rewrite HE0, HM0 in Huz. change ((0 =? 0) && (0 =? 0)) with true in Huz.
        unfold cvtV, cvtFlags; cbv zeta. rewrite Hun, Hui, Huz, Hsg. cbv iota.
        destruct (toB1 a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
        destruct C as (-> & _). cbn [cvtB]. rewrite (ofB_zero e2 f2 Hf2 Hpe2). split; reflexivity.
      + destruct (cvt_main rm a s E M HM HE Ha HE1 Hz) as (R1 & R2).
        rewrite R1, R2. unfold cvtFlags.
        destruct (toB1 a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
        split; reflexivity.
  Qed.
End CvtFF.
