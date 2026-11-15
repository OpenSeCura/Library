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
 * FDIV against Flocq's `Bdiv` (`Div.v`).
 *
 * `fdivRef rm a b` is the reference core (`FpCoreRef.fpuComputeRef`) on a decoded FDIV.
 * `fdiv_flocq`: its result is Flocq's `Bdiv` (in `BinarySingleNaN`, NaN encoded as the RISC-V
 * canonical NaN) and its flags are the IEEE flags of rounding the exact quotient (`Flags.v`), with
 * NV for a signaling NaN operand, `inf / inf` or `0 / 0`, and DZ for a finite non-zero dividend
 * divided by zero.
 *
 * The core computes `q = floor(siga * 2^(f+2) / sigb)` and a sticky bit (remainder non-zero), then
 * `normRound` with the window `W = f + 3`.  When `q` has only `f + 2` bits, `normRound` shifts it
 * left by one with a zero LSB; the exact location of the quotient is then given by the one-bit
 * longer quotient `floor(siga * 2^(f+3) / sigb)`, and `rp_congr` shows that the integer rounding
 * model gives the same result and flags for both.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Flocq Require Calc.Div.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ---------------------------------------------------------------------------
 * `normRound` for a window `W >= f + 3` (DIV uses `W = f + 3`)
 * --------------------------------------------------------------------------- *)

Section NormW.
  Variable e f : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  (* `NormRound.normRound_eval` with `f + 3 <= W` instead of `f + 4 <= W` (same proof). *)
  Lemma normRound_evalW : forall W s x wsig st rm,
    f + 3 <= W -> W < 2 ^ (e + 2) -> 0 < Zmod.to_Z wsig ->
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

  (* The DIV window `W = f + 3`: no low bits are dropped (`d = 0`). *)
  Lemma normRound_f3 : forall s x wsig st rm,
    0 < Zmod.to_Z wsig -> - 2 ^ (e + 2) <= Zmod.signed x - (f + 3) ->
    evalLetExpr (normRound false e f type (f + 3) s x wsig st rm) =
    evalLetExpr (roundPack false e f type s (Zmod.of_Z _ (Zmod.signed x - (f + 2 - Z.log2 (Zmod.to_Z wsig))))
                   (Zmod.of_Z _ (Zmod.to_Z wsig * 2 ^ (f + 2 - Z.log2 (Zmod.to_Z wsig)))) st rm).
  Proof.
    intros s x wsig st rm Hw Hx.
    assert (HW2 : f + 3 < 2 ^ (e + 2)).
    { assert (2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
      lia. }
    pose proof (normRound_evalW (f + 3) s x wsig st rm ltac:(lia) HW2 Hw Hx) as R; cbv zeta in R. rewrite R.
    replace (f + 3 - (f + 3)) with 0 by lia. replace (f + 3 - 1 - Z.log2 (Zmod.to_Z wsig)) with (f + 2 - Z.log2 (Zmod.to_Z wsig)) by lia.
    rewrite Z.pow_0_r, Z.div_1_r, Z.mod_1_r. cbn [Z.eqb negb]. rewrite orb_false_r. reflexivity.
  Qed.
End NormW.

(* ---------------------------------------------------------------------------
 * The integer rounding model only depends on `S / 2` and `bit0 S || st`
 * --------------------------------------------------------------------------- *)

Lemma testbit_succ_div2 : forall S m, 0 <= m -> Z.testbit S (m + 1) = Z.testbit (S / 2) m.
Proof. intros S m Hm. rewrite <- (Z.div_pow2_bits S 1 m) by lia. reflexivity. Qed.

Lemma sticky_split : forall S st sh, 0 <= S -> 0 < sh ->
  Z.testbit (S / 2 ^ sh) 0 || (st || negb (S mod 2 ^ sh =? 0)) =
  Z.testbit (S / 2) (sh - 1) || (Z.testbit S 0 || st) || negb ((S / 2) mod 2 ^ (sh - 1) =? 0).
Proof.
  intros S st sh HS Hsh.
  rewrite Z.div_pow2_bits by lia. replace (0 + sh) with ((sh - 1) + 1) by lia. rewrite testbit_succ_div2 by lia.
  assert (Hp : 2 ^ sh = 2 * 2 ^ (sh - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hp1 : 0 < 2 ^ (sh - 1)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Hp, Z.rem_mul_r by lia.
  pose proof (Z.bit0_mod S) as B.
  set (m := (S / 2) mod 2 ^ (sh - 1)).
  assert (Hm : 0 <= m) by (apply Z.mod_pos_bound; lia).
  destruct (Z.testbit S 0); cbn [Z.b2z] in B; rewrite <- B.
  - replace (1 + 2 * m =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct st, (Z.testbit (S / 2) (sh - 1)); reflexivity.
  - destruct (Z.eqb_spec m 0) as [E | E].
    + rewrite E. destruct st, (Z.testbit (S / 2) (sh - 1)); reflexivity.
    + replace (0 + 2 * m =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct st, (Z.testbit (S / 2) (sh - 1)); reflexivity.
Qed.

Section Congr.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.

  Lemma rp_congr : forall rmz s X S1 S2 st1 st2, 0 <= S1 -> 0 <= S2 -> S1 / 2 = S2 / 2 ->
    (Z.testbit S1 0 || st1) = (Z.testbit S2 0 || st2) ->
    rpRes e f rmz s X S1 st1 = rpRes e f rmz s X S2 st2 /\ rpOvf e f rmz s X S1 st1 = rpOvf e f rmz s X S2 st2 /\
    rpUf e f rmz s X S1 st1 = rpUf e f rmz s X S2 st2 /\ rpNx e f rmz s X S1 st1 = rpNx e f rmz s X S2 st2.
  Proof.
    intros rmz s X S1 S2 st1 st2 H1 H2 Hd Hb.
    assert (Hsh : 0 <= rpSh e f X)
      by (unfold rpSh; destruct (rpTiny e X) eqn:Ht; [unfold rpTiny in Ht; apply Z.ltb_lt in Ht; lia | lia]).
    assert (Hp : 0 < 2 ^ rpSh e f X) by (apply Z.pow_pos_nonneg; lia).
    assert (K1 : rpSigS e f X S1 / 4 = rpSigS e f X S2 / 4).
    { unfold rpSigS. rewrite !Z.div_div by lia.
      replace (2 ^ rpSh e f X * 4) with (2 * (2 ^ rpSh e f X * 2)) by lia.
      rewrite <- !Z.div_div by lia. rewrite Hd; reflexivity. }
    assert (K2 : forall j, 1 <= j -> Z.testbit (rpSigS e f X S1) j = Z.testbit (rpSigS e f X S2) j).
    { intros j Hj; unfold rpSigS. rewrite !Z.div_pow2_bits by lia.
      replace (j + rpSh e f X) with ((j + rpSh e f X - 1) + 1) by lia.
      rewrite !testbit_succ_div2 by lia. rewrite Hd; reflexivity. }
    assert (K3 : rpR e f X S1 st1 = rpR e f X S2 st2).
    { unfold rpR, rpStS, rpSigS.
      destruct (Z.eq_dec (rpSh e f X) 0) as [E0 | E0].
      - rewrite E0, Z.pow_0_r, !Z.div_1_r, !Z.mod_1_r. cbn [Z.eqb negb]. rewrite !orb_false_r. exact Hb.
      - rewrite !sticky_split by lia. rewrite Hd, Hb. reflexivity. }
    assert (K4 : rpInc e f rmz s X S1 st1 = rpInc e f rmz s X S2 st2).
    { unfold rpInc, rpG. rewrite (K2 2), (K2 1), K3 by lia. reflexivity. }
    assert (K5 : rpRnd e f rmz s X S1 st1 = rpRnd e f rmz s X S2 st2) by (unfold rpRnd; rewrite K1, K4; reflexivity).
    assert (K6 : rpOvf e f rmz s X S1 st1 = rpOvf e f rmz s X S2 st2) by (unfold rpOvf, rpMagW; rewrite K5; reflexivity).
    assert (K7 : rpInexact e f X S1 st1 = rpInexact e f X S2 st2) by (unfold rpInexact, rpG; rewrite (K2 1), K3 by lia; reflexivity).
    assert (K8 : rpCarry0 f rmz s S1 st1 = rpCarry0 f rmz s S2 st2).
    { assert (T1 : forall S, Z.testbit S 1 = Z.testbit (S / 2) 0) by (intros S; apply (testbit_succ_div2 S 0); lia).
      assert (T2 : forall S, Z.testbit S 2 = Z.testbit (S / 2) 1) by (intros S; apply (testbit_succ_div2 S 1); lia).
      assert (D4 : forall S, S / 4 = S / 2 / 2) by (intros S; rewrite Z.div_div by lia; reflexivity).
      unfold rpCarry0. rewrite !T1, !T2, (D4 S1), (D4 S2), Hd, Hb. reflexivity. }
    split; [| split; [exact K6 | split]].
    - unfold rpRes, rpMag. rewrite K6. unfold rpMagW. rewrite K5. reflexivity.
    - unfold rpUf. rewrite K8, K7, K6. reflexivity.
    - unfold rpNx. rewrite K7, K6. reflexivity.
  Qed.
End Congr.

(* ---------------------------------------------------------------------------
 * Small real / location helpers
 * --------------------------------------------------------------------------- *)

Lemma new_loc_exact : forall n r, new_location n r loc_Exact = loc_Exact <-> negb (r =? 0) = false.
Proof.
  intros n r. unfold new_location, new_location_even, new_location_odd.
  destruct (Z.eqb_spec r 0) as [-> | Hr].
  - destruct (Z.even n); cbn; tauto.
  - assert (E : (r =? 0) = false) by (apply Z.eqb_neq; exact Hr).
    destruct (Z.even n); cbv beta; rewrite E; cbn; split; intros H; discriminate H.
Qed.

Lemma div_sign : forall sa sb A B, (0 < A)%R -> (0 < B)%R ->
  (cond_Ropp sa A / cond_Ropp sb B)%R = cond_Ropp (xorb sa sb) (A / B).
Proof. intros sa sb A B HA HB; destruct sa, sb; cbn [cond_Ropp xorb]; field; intros H; lra. Qed.

Lemma sign_cond : forall s P, (0 < P)%R -> Rlt_bool (cond_Ropp s P) 0 = s.
Proof. intros s P HP; destruct s; cbn [cond_Ropp]; [apply Rlt_bool_true | apply Rlt_bool_false]; lra. Qed.

Lemma fin_not_nan : forall prec emax (b : BinarySingleNaN.binary_float prec emax),
  BinarySingleNaN.is_finite b = true -> BinarySingleNaN.is_nan b = false.
Proof. intros prec emax [| | |]; cbn; easy. Qed.

(* `Fdiv_core`: the quotient `floor(Sa * 2^(f+2+k) / Sb)` locates `Sa 2^(Xa-f) / (Sb 2^(Xb-f))` at
 * exponent `Xa - Xb - k - f - 2`, exactly iff the remainder is zero. *)
Lemma div_loc : forall f Sa Sb Xa Xb k, 0 <= f -> 0 < Sa -> 0 < Sb -> 0 <= k ->
  exists l, inbetween_float radix2 (Sa * 2 ^ (f + 2 + k) / Sb) (Xa - Xb - k - f - 2)
              (F2R (Float radix2 Sa (Xa - f)) / F2R (Float radix2 Sb (Xb - f))) l /\
            (l = loc_Exact <-> negb ((Sa * 2 ^ (f + 2 + k)) mod Sb =? 0) = false).
Proof.
  intros f Sa Sb Xa Xb k Hf HSa HSb Hk.
  pose proof (Flocq.Calc.Div.Fdiv_core_correct radix2 Sa (Xa - f) Sb (Xb - f) (Xa - Xb - k - f - 2) HSa HSb) as C.
  unfold Flocq.Calc.Div.Fdiv_core in C.
  assert (Hle : Z.leb (Xa - Xb - k - f - 2) (Xa - f - (Xb - f)) = true) by (apply Z.leb_le; lia).
  rewrite Hle in C.
  replace (Xa - f - (Xb - f) - (Xa - Xb - k - f - 2)) with (f + 2 + k) in C by lia.
  cbv beta iota in C.
  change (Zpower radix2 (f + 2 + k)) with (2 ^ (f + 2 + k)) in C.
  assert (E : Z.div_eucl (Sa * 2 ^ (f + 2 + k)) Sb = (Sa * 2 ^ (f + 2 + k) / Sb, Sa * 2 ^ (f + 2 + k) mod Sb))
    by (unfold Z.div, Z.modulo; destruct (Z.div_eucl _ _); reflexivity).
  rewrite E in C. cbv beta iota in C.
  eexists; split; [exact C | apply new_loc_exact].
Qed.

(* ---------------------------------------------------------------------------
 * FDIV
 * --------------------------------------------------------------------------- *)

Section Div.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).
  Local Abbreviation isSNaN := (isSNaN e f Hf Hpe).

  (* Flocq's side conditions, as the instances its operations expect. *)
  Local Instance precGt : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  (* The decoded FDIV (`FpCore.FpOpDK`): only the `div` family flag is set. *)
  Definition opDiv : type FpOpDK :=
    (false ,, (false ,, (false ,, (true ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (false ,, (false ,, (false ,, tt)))))))))))))))))))))).

  (* FDIV in the reference core. *)
  Definition fdivRef (rm : bits 3) (a b : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqOf e f xlen opDiv rm a b Zmod.zero Zmod.zero)).

  (* IEEE flags of FDIV. *)
  Definition divFlags (rm : bits 3) (a b : bits W) : bits 5 :=
    match toB a, toB b with
    | BinarySingleNaN.B754_nan, _ | _, BinarySingleNaN.B754_nan =>
        mkFl (isSNaN a || isSNaN b) false false false false
    | BinarySingleNaN.B754_infinity _, BinarySingleNaN.B754_infinity _
    | BinarySingleNaN.B754_zero _, BinarySingleNaN.B754_zero _ => mkFl true false false false false
    | BinarySingleNaN.B754_finite _ _ _ _, BinarySingleNaN.B754_zero _ => mkFl false true false false false
    | BinarySingleNaN.B754_finite _ _ _ _, BinarySingleNaN.B754_finite _ _ _ _ =>
        finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
          (Rdiv (BinarySingleNaN.B2R (toB a)) (BinarySingleNaN.B2R (toB b)))
    | _, _ => mkFl false false false false false
    end.

  Definition fdiv_flocq : Prop :=
    forall rm a b,
      (fdivRef rm a b) @% "res" = ofB (BinarySingleNaN.Bdiv (modeOf rm) (toB a) (toB b)) /\
      (fdivRef rm a b) @% "flags" = divFlags rm a b.

  (* ---------------------------------------------------------------------------
   * The FDIV path of the core
   * --------------------------------------------------------------------------- *)

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  (* Quotient, sticky bit and exponent of `divSpec` / `divFinishCore`. *)
  Definition qOf (siga sigb : bits (f + 1)) : bits (f + 3) :=
    evalExpr (trunc (2 * f + 3) (f + 3) (Div (Var type (Bit (2 * f + 3)) (evalExpr (divNumer f type siga)))
                                              (Var type (Bit (2 * f + 3)) (evalExpr (divDenom f type sigb))))).

  Definition stOf (siga sigb : bits (f + 1)) : bool :=
    evalExpr (isNotZero (Rem (Var type (Bit (2 * f + 3)) (evalExpr (divNumer f type siga)))
                             (Var type (Bit (2 * f + 3)) (evalExpr (divDenom f type sigb))))).

  Definition xqOf (ea eb : bits (e + 3)) : bits (e + 3) :=
    evalExpr (Add [Sub (Var type (Bit (e + 3)) ea) (Var type (Bit (e + 3)) eb); cst (e + 3) (expOff false e)]).

  (* `divSpec false`, transcribed. *)
  Definition divV (rm : bits 3) (ua ub : type (FpUnpK e f)) : type (FpOutK e f) :=
    let s := xorb (uSign ua) (uSign ub) in
    let inv := (uInf ua && uInf ub) || (uZero ua && uZero ub) in
    let nv := uSNaN ua || uSNaN ub || inv in
    if (uNaN ua || uNaN ub) || inv
    then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if uInf ua then (evalExpr (infE e f type (ConstBool s)) ,, (Zmod.of_Z _ 0 ,, tt))
    else if uInf ub then (evalExpr (zeroE e f type (ConstBool s)) ,, (Zmod.of_Z _ 0 ,, tt))
    else if uZero ua then (evalExpr (zeroE e f type (ConstBool s)) ,, (Zmod.of_Z _ 0 ,, tt))
    else if uZero ub then (evalExpr (infE e f type (ConstBool s)) ,,
                           (evalExpr (mkFlags type (ConstBool false) (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else evalLetExpr (normRound false e f type (f + 3) s (xqOf (uExp ua) (uExp ub)) (qOf (uSig ua) (uSig ub))
                                (stOf (uSig ua) (uSig ub)) rm).

  Lemma fdiv_core_res : forall rm a b, (fdivRef rm a b) @% "res" = (divV rm (unp a) (unp b)).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma fdiv_core_flags : forall rm a b, (fdivRef rm a b) @% "flags" = (divV rm (unp a) (unp b)).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  (* ---------------------------------------------------------------------------
   * Bit-vector values
   * --------------------------------------------------------------------------- *)

  Lemma HeD : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Lemma mkFlags_eval : forall nv dz ov uf nx,
    evalExpr (mkFlags type (ConstBool nv) (ConstBool dz) (ConstBool ov) (ConstBool uf) (ConstBool nx)) = mkFl nv dz ov uf nx.
  Proof. intros [|] [|] [|] [|] [|]; vm_compute; reflexivity. Qed.

  Lemma nn_val : forall siga : bits (f + 1),
    Zmod.to_Z (evalExpr (divNumer f type siga)) = Zmod.to_Z siga * 2 ^ (f + 2).
  Proof.
    intros siga. pose proof (bits.unsigned_range siga ltac:(lia)) as Hs.
    assert (H2 : 2 ^ (2 * f + 3) = 2 ^ (f + 1) * 2 ^ (f + 2)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hlt : f + 2 < 2 ^ (2 * f + 3)) by (pose proof (Z.pow_gt_lin_r 2 (2 * f + 3) ltac:(lia) ltac:(lia)); lia).
    assert (0 < 2 ^ (f + 2)) by (apply Z.pow_pos_nonneg; lia).
    unfold divNumer; cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr cst].
    rewrite (tz_ofZ (2 * f + 3) (f + 2)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    apply Z.mod_small. split; [nia |]. rewrite H2. apply Z.mul_lt_mono_pos_r; lia.
  Qed.

  Lemma dd_val : forall sigb : bits (f + 1), Zmod.to_Z (evalExpr (divDenom f type sigb)) = Zmod.to_Z sigb.
  Proof. intros sigb. unfold divDenom. rewrite unsigned_zext by lia. reflexivity. Qed.

  Section Sig.
    Variables siga sigb : bits (f + 1).
    Hypothesis HSa : 2 ^ f <= Zmod.to_Z siga < 2 ^ (f + 1).
    Hypothesis HSb : 2 ^ f <= Zmod.to_Z sigb < 2 ^ (f + 1).

    Lemma q_range : 2 ^ (f + 1) <= Zmod.to_Z siga * 2 ^ (f + 2) / Zmod.to_Z sigb < 2 ^ (f + 3).
    Proof.
      assert (P1 : 2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
      assert (P2 : 2 ^ (f + 2) = 2 * 2 ^ (f + 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      assert (P3 : 2 ^ (f + 3) = 2 * 2 ^ (f + 2)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      assert (0 < 2 ^ f) by (apply Z.pow_pos_nonneg; lia).
      split.
      - apply Z.div_le_lower_bound; [lia |].
        assert (2 ^ (f + 1) * Zmod.to_Z sigb <= 2 ^ (f + 1) * 2 ^ (f + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (2 ^ f * 2 ^ (f + 2) <= Zmod.to_Z siga * 2 ^ (f + 2)) by (apply Z.mul_le_mono_nonneg_r; lia).
        nia.
      - apply Z.div_lt_upper_bound; [lia |].
        assert (Zmod.to_Z siga * 2 ^ (f + 2) < 2 ^ (f + 1) * 2 ^ (f + 2)) by (apply Z.mul_lt_mono_pos_r; lia).
        assert (2 ^ (f + 3) * 2 ^ f <= 2 ^ (f + 3) * Zmod.to_Z sigb) by (apply Z.mul_le_mono_nonneg_l; lia).
        nia.
    Qed.

    Lemma q_val : Zmod.to_Z (qOf siga sigb) = Zmod.to_Z siga * 2 ^ (f + 2) / Zmod.to_Z sigb.
    Proof.
      pose proof q_range.
      unfold qOf. rewrite unsigned_trunc by lia. cbn [evalExpr].
      rewrite Zmod.unsigned_udiv_nonneg by (try (apply Z.pow_nonneg; lia); rewrite dd_val; lia).
      rewrite nn_val, dd_val. apply Z.mod_small. lia.
    Qed.

    Lemma st_val : stOf siga sigb = negb ((Zmod.to_Z siga * 2 ^ (f + 2)) mod Zmod.to_Z sigb =? 0).
    Proof.
      unfold stOf. rewrite evalExpr_isNotZero_bits. cbn [evalExpr].
      rewrite Zmod.unsigned_umod, nn_val, dd_val. reflexivity.
    Qed.
  End Sig.

  Lemma xq_val : forall ea eb : bits (e + 3),
    - 2 ^ (e - 1) - f <= Zmod.signed ea <= 2 ^ (e - 1) -> - 2 ^ (e - 1) - f <= Zmod.signed eb <= 2 ^ (e - 1) ->
    Zmod.signed (xqOf ea eb) = Zmod.signed ea - Zmod.signed eb.
  Proof.
    intros ea eb Ha Hb. pose proof HeD.
    unfold xqOf. cbn [evalExpr fold_left map cst]. rewrite (sub_eval (e + 3) ltac:(lia)). cbn [evalExpr]. unfold expOff.
    rewrite <- (Zmod.of_Z_signed ea) at 1. rewrite <- (Zmod.of_Z_signed eb) at 1.
    rewrite <- (Zmod.of_Z_0 (2 ^ (e + 3))), <- Zmod.of_Z_sub, <- !Zmod.of_Z_add.
    rewrite Z.add_0_l, Z.add_0_r. apply signed_of_Z_small; [lia |].
    replace (e + 3 - 1) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; change (2 ^ 3) with 8; lia.
  Qed.

  (* ---------------------------------------------------------------------------
   * Normalization shift and the one-bit-longer quotient
   * --------------------------------------------------------------------------- *)

  (* `q` has `f + 2` or `f + 3` bits: the normalization shift is 1 or 0. *)
  Lemma k_cases : forall Q, 2 ^ (f + 1) <= Q < 2 ^ (f + 3) ->
    exists k, (k = 0 \/ k = 1) /\ f + 2 - Z.log2 Q = k /\ 2 ^ (f + 2) <= Q * 2 ^ k < 2 ^ (f + 3).
  Proof.
    intros Q HQ.
    assert (P2 : 2 ^ (f + 2) = 2 * 2 ^ (f + 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (P3 : 2 ^ (f + 3) = 2 * 2 ^ (f + 2)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    destruct (Z_lt_le_dec Q (2 ^ (f + 2))) as [H | H].
    - exists 1. rewrite (Z.log2_unique Q (f + 1)) by (try lia; replace (Z.succ (f + 1)) with (f + 2) by lia; lia).
      change (2 ^ 1) with 2. split; [right; reflexivity | split; lia].
    - exists 0. rewrite (Z.log2_unique Q (f + 2)) by (try lia; replace (Z.succ (f + 2)) with (f + 3) by lia; lia).
      rewrite Z.pow_0_r. split; [left; reflexivity | split; lia].
  Qed.

  (* Rounding `q * 2^k` with the sticky bit of `q` is rounding the `f + 2 + k`-bit quotient with its own
   * sticky bit; both have the same half. *)
  Lemma congr_k : forall rmz s X Sa Sb k, 0 < Sa -> 0 < Sb -> (k = 0 \/ k = 1) ->
    rpRes e f rmz s X (Sa * 2 ^ (f + 2) / Sb * 2 ^ k) (negb ((Sa * 2 ^ (f + 2)) mod Sb =? 0)) =
    rpRes e f rmz s X (Sa * 2 ^ (f + 2 + k) / Sb) (negb ((Sa * 2 ^ (f + 2 + k)) mod Sb =? 0)) /\
    rpOvf e f rmz s X (Sa * 2 ^ (f + 2) / Sb * 2 ^ k) (negb ((Sa * 2 ^ (f + 2)) mod Sb =? 0)) =
    rpOvf e f rmz s X (Sa * 2 ^ (f + 2 + k) / Sb) (negb ((Sa * 2 ^ (f + 2 + k)) mod Sb =? 0)) /\
    rpUf e f rmz s X (Sa * 2 ^ (f + 2) / Sb * 2 ^ k) (negb ((Sa * 2 ^ (f + 2)) mod Sb =? 0)) =
    rpUf e f rmz s X (Sa * 2 ^ (f + 2 + k) / Sb) (negb ((Sa * 2 ^ (f + 2 + k)) mod Sb =? 0)) /\
    rpNx e f rmz s X (Sa * 2 ^ (f + 2) / Sb * 2 ^ k) (negb ((Sa * 2 ^ (f + 2)) mod Sb =? 0)) =
    rpNx e f rmz s X (Sa * 2 ^ (f + 2 + k) / Sb) (negb ((Sa * 2 ^ (f + 2 + k)) mod Sb =? 0)) /\
    Sa * 2 ^ (f + 2 + k) / Sb / 2 = Sa * 2 ^ (f + 2) / Sb * 2 ^ k / 2.
  Proof.
    intros rmz s X Sa Sb k HSa HSb [-> | ->].
    - rewrite Z.add_0_r, Z.pow_0_r, Z.mul_1_r. repeat split; reflexivity.
    - change (2 ^ 1) with 2.
      replace (Sa * 2 ^ (f + 2 + 1)) with (2 * (Sa * 2 ^ (f + 2))) by (rewrite (Z.pow_add_r 2 (f + 2) 1) by lia; change (2 ^ 1) with 2; ring).
      set (N := Sa * 2 ^ (f + 2)).
      assert (HN : 0 < N) by (unfold N; pose proof (Z.pow_pos_nonneg 2 (f + 2) ltac:(lia) ltac:(lia)); nia).
      pose proof (Z.div_mod N Sb ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound N Sb HSb) as Hmb.
      assert (Hq : 0 <= N / Sb) by (apply Z.div_pos; lia).
      set (q := N / Sb) in *. set (r := N mod Sb) in *.
      rewrite (Z.mul_comm q 2).
      assert (D0 : 2 * q / 2 = q) by (symmetry; apply Z.div_unique with 0; lia).
      destruct (Z_lt_le_dec (2 * r) Sb) as [Hr | Hr].
      + assert (E1 : 2 * N / Sb = 2 * q) by (symmetry; apply Z.div_unique with (2 * r); lia).
        assert (E2 : (2 * N) mod Sb = 2 * r) by (symmetry; apply Z.mod_unique with (2 * q); lia).
        rewrite E1, E2.
        assert (Hb : (Z.testbit (2 * q) 0 || negb (r =? 0)) = (Z.testbit (2 * q) 0 || negb (2 * r =? 0))).
        { rewrite Z.testbit_even_0. destruct (Z.eqb_spec r 0); destruct (Z.eqb_spec (2 * r) 0); cbn; try reflexivity; exfalso; lia. }
        destruct (rp_congr e f Hf rmz s X (2 * q) (2 * q) _ _ ltac:(lia) ltac:(lia) eq_refl Hb) as (C1 & C2 & C3 & C4).
        repeat split; assumption || reflexivity.
      + assert (E1 : 2 * N / Sb = 2 * q + 1) by (symmetry; apply Z.div_unique with (2 * r - Sb); lia).
        assert (E2 : (2 * N) mod Sb = 2 * r - Sb) by (symmetry; apply Z.mod_unique with (2 * q + 1); lia).
        rewrite E1, E2.
        assert (D1 : (2 * q + 1) / 2 = q) by (symmetry; apply Z.div_unique with 1; lia).
        assert (Hb : (Z.testbit (2 * q) 0 || negb (r =? 0)) = (Z.testbit (2 * q + 1) 0 || negb (2 * r - Sb =? 0))).
        { rewrite Z.testbit_even_0, Z.testbit_odd_0. destruct (Z.eqb_spec r 0); [exfalso; lia | reflexivity]. }
        destruct (rp_congr e f Hf rmz s X (2 * q) (2 * q + 1) _ _ ltac:(lia) ltac:(lia) ltac:(lia) Hb) as (C1 & C2 & C3 & C4).
        repeat split; try assumption. lia.
  Qed.

  (* ---------------------------------------------------------------------------
   * Finite non-zero operands
   * --------------------------------------------------------------------------- *)

  Lemma rpZ : forall s x sigR st rm,
    evalLetExpr (roundPack false e f type s x sigR st rm) =
    (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) s (Zmod.signed x) (Zmod.to_Z sigR) st) ,,
     (mkFl false false (rpOvf e f (Zmod.to_Z rm) s (Zmod.signed x) (Zmod.to_Z sigR) st)
                       (rpUf e f (Zmod.to_Z rm) s (Zmod.signed x) (Zmod.to_Z sigR) st)
                       (rpNx e f (Zmod.to_Z rm) s (Zmod.signed x) (Zmod.to_Z sigR) st) ,, tt)).
  Proof. intros; exact (roundPack_Z e f HeD Hf Hpe s x sigR st rm). Qed.

  Lemma div_fin_core : forall rm (x y : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) sa sb
      (siga sigb : bits (f + 1)) (ea eb : bits (e + 3)),
    2 ^ f <= Zmod.to_Z siga < 2 ^ (f + 1) -> 2 ^ f <= Zmod.to_Z sigb < 2 ^ (f + 1) ->
    fpEmin e - f <= Zmod.signed ea <= fpEmax e -> fpEmin e - f <= Zmod.signed eb <= fpEmax e ->
    BinarySingleNaN.B2R x = cond_Ropp sa (F2R (Float radix2 (Zmod.to_Z siga) (Zmod.signed ea - f))) ->
    BinarySingleNaN.B2R y = cond_Ropp sb (F2R (Float radix2 (Zmod.to_Z sigb) (Zmod.signed eb - f))) ->
    BinarySingleNaN.is_finite x = true -> BinarySingleNaN.Bsign x = sa -> BinarySingleNaN.Bsign y = sb ->
    let o := evalLetExpr (normRound false e f type (f + 3) (xorb sa sb) (xqOf ea eb) (qOf siga sigb) (stOf siga sigb) rm) in
    o.(Fst) = ofB (BinarySingleNaN.Bdiv (modeOf rm) x y) /\
    o.(Snd).(Fst) = finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) (Rdiv (BinarySingleNaN.B2R x) (BinarySingleNaN.B2R y)).
  Proof.
    intros rm x y sa sb siga sigb ea eb HSa HSb HXa HXb HVa HVb HFa HSga HSgb o.
    pose proof HeD as He.
    assert (HE2 : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (P0 : 0 < 2 ^ f) by (apply Z.pow_pos_nonneg; lia).
    assert (P1 : 0 < 2 ^ (f + 1)) by (apply Z.pow_pos_nonneg; lia).
    unfold fpEmin, fpEmax, fpBias in HXa, HXb.
    pose proof (q_range siga sigb HSa HSb) as HQr. pose proof (q_val siga sigb HSa HSb) as HQ.
    pose proof (st_val siga sigb) as HST.
    pose proof (xq_val ea eb ltac:(lia) ltac:(lia)) as HXQ.
    set (Sa := Zmod.to_Z siga) in *. set (Sb := Zmod.to_Z sigb) in *.
    set (Xa := Zmod.signed ea) in *. set (Xb := Zmod.signed eb) in *.
    unfold o; clear o.
    rewrite (normRound_f3 e f He Hf Hpe) by (rewrite ?HQ, ?HXQ; lia).
    rewrite rpZ. cbn [Fst Snd].
    rewrite HQ, HXQ, HST.
    set (Q := Sa * 2 ^ (f + 2) / Sb) in *.
    destruct (k_cases Q HQr) as (k & Hk01 & Hkeq & HQk). rewrite Hkeq.
    rewrite (signed_k e He) by lia. rewrite (tz_ofZ (f + 3)) by lia.
    destruct (congr_k (Zmod.to_Z rm) (xorb sa sb) (Xa - Xb - k) Sa Sb k ltac:(lia) ltac:(lia) Hk01) as (C1 & C2 & C3 & C4 & C5).
    fold Q in C1, C2, C3, C4, C5. rewrite C1, C2, C3, C4.
    set (S' := Sa * 2 ^ (f + 2 + k) / Sb) in *. set (st' := negb ((Sa * 2 ^ (f + 2 + k)) mod Sb =? 0)).
    assert (HS' : 2 ^ (f + 2) <= S' < 2 ^ (f + 3)).
    { assert (P2 : 2 ^ (f + 2) = 2 * 2 ^ (f + 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      assert (P3 : 2 ^ (f + 3) = 2 * 2 ^ (f + 2)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      pose proof (Z.div_mod S' 2 ltac:(lia)). pose proof (Z.mod_pos_bound S' 2 ltac:(lia)).
      pose proof (Z.div_mod (Q * 2 ^ k) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (Q * 2 ^ k) 2 ltac:(lia)).
      lia. }
    destruct (div_loc f Sa Sb Xa Xb k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (l0 & Hin & Hl0).
    fold S' st' in Hin, Hl0.
    assert (HA : (0 < F2R (Float radix2 Sa (Xa - f)))%R) by (apply F2R_gt_0; cbn; lia).
    assert (HB : (0 < F2R (Float radix2 Sb (Xb - f)))%R) by (apply F2R_gt_0; cbn; lia).
    assert (HAB : (0 < F2R (Float radix2 Sa (Xa - f)) / F2R (Float radix2 Sb (Xb - f)))%R)
      by (apply Rdiv_lt_0_compat; assumption).
    set (v := Rdiv (BinarySingleNaN.B2R x) (BinarySingleNaN.B2R y)).
    assert (Hv : v = cond_Ropp (xorb sa sb) (F2R (Float radix2 Sa (Xa - f)) / F2R (Float radix2 Sb (Xb - f))))
      by (unfold v; rewrite HVa, HVb; apply div_sign; assumption).
    assert (Hin' : inbetween_float radix2 S' (Xa - Xb - k - f - 2) (Rabs v) l0)
      by (rewrite Hv, abs_cond_Ropp, Rabs_pos_eq by lra; exact Hin).
    assert (Hs : Rlt_bool v 0 = xorb sa sb) by (rewrite Hv; apply sign_cond; exact HAB).
    assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)) as Hr; change (2 ^ 3) with 8 in Hr; exact Hr).
    assert (Hy0 : BinarySingleNaN.B2R y <> 0%R) by (rewrite HVb; destruct sb; cbn [cond_Ropp]; lra).
    pose proof (@BinarySingleNaN.Bdiv_correct _ _ _ _ (modeOf rm) x y Hy0) as HBd.
    fold v in HBd. rewrite HSga, HSgb in HBd.
    change (modeOf rm) with (modeZ (Zmod.to_Z rm)) in HBd |- *.
    split.
    - assert (Hres : toB (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) (xorb sa sb) (Xa - Xb - k) S' st')) =
                     BinarySingleNaN.Bdiv (modeZ (Zmod.to_Z rm)) x y).
      { apply (rp_result e f Hf Hpe _ _ _ _ _ v l0 Hrm HS' Hin' Hl0 Hs).
        revert HBd. match goal with |- (if ?c then _ else _) -> _ => destruct c end; intros HBd.
        - destruct HBd as (H1 & H2 & H3).
          assert (Hfin : BinarySingleNaN.is_finite (BinarySingleNaN.Bdiv (modeZ (Zmod.to_Z rm)) x y) = true)
            by (rewrite H2; exact HFa).
          split; [exact H1 | split; [exact Hfin |]]. apply H3, fin_not_nan, Hfin.
        - exact HBd. }
      assert (Hnn : BinarySingleNaN.is_nan (BinarySingleNaN.Bdiv (modeZ (Zmod.to_Z rm)) x y) = false).
      { revert HBd. match goal with |- (if ?c then _ else _) -> _ => destruct c end; intros HBd.
        - destruct HBd as (_ & H2 & _). apply fin_not_nan. rewrite H2; exact HFa.
        - rewrite (is_nan_B2SF e f), HBd. unfold BinarySingleNaN.binary_overflow.
          destruct (BinarySingleNaN.overflow_to_inf _ _); reflexivity. }
      rewrite <- Hres. rewrite ofB_toB; [reflexivity |]. rewrite Hres; exact Hnn.
    - unfold finiteFlags. rewrite (rp_flags e f Hf Hpe _ _ _ _ _ v l0 Hrm HS' Hin' Hl0 Hs). reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * Classes of the operands
   * --------------------------------------------------------------------------- *)

  Lemma classify : forall (x : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    uSign (unp x) = s /\ uSNaN (unp x) = isSNaN x /\
    ((toB x = BinarySingleNaN.B754_zero s /\ uZero (unp x) = true /\ uInf (unp x) = false /\
      uNaN (unp x) = false /\ isSNaN x = false) \/
     (toB x = BinarySingleNaN.B754_infinity s /\ uZero (unp x) = false /\ uInf (unp x) = true /\
      uNaN (unp x) = false /\ isSNaN x = false) \/
     (toB x = BinarySingleNaN.B754_nan /\ uZero (unp x) = false /\ uInf (unp x) = false /\ uNaN (unp x) = true) \/
     ((exists m ex Hb, toB x = BinarySingleNaN.B754_finite s m ex Hb) /\ uZero (unp x) = false /\
      uInf (unp x) = false /\ uNaN (unp x) = false /\ isSNaN x = false /\ E <> 2 ^ e - 1 /\ (E <> 0 \/ M <> 0))).
  Proof.
    intros x s E M HM HE Hx. pose proof HeD as He0. cbv beta.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    pose proof (cls e f Hf Hpe x s E M HM HE Hx) as C.
    rewrite (u_sign e f He0 Hf x s E M HM HE Hx), (u_snan e f He0 Hf x s E M HM HE Hx), (u_zero e f He0 Hf x s E M HM HE Hx),
      (u_inf e f He0 Hf x s E M HM HE Hx), (u_nan e f He0 Hf x s E M HM HE Hx), (isSNaN_eq e f Hf Hpe x s E M HM HE Hx).
    split; [reflexivity |]; split; [reflexivity |].
    destruct (toB x) as [s' | s' | | s' m ex Hb]; cbn [clsP] in C;
      destruct (Z.eqb_spec E 0); destruct (Z.eqb_spec M 0); destruct (Z.eqb_spec E (2 ^ e - 1)); cbn [andb negb];
      try (exfalso; lia).
    all: first
      [ solve [left; destruct C as (-> & _ & _); repeat split]
      | solve [right; left; destruct C as (-> & _ & _); repeat split]
      | solve [right; right; left; repeat split]
      | solve [right; right; right; destruct C as (-> & _); split; [exists m, ex, Hb; reflexivity | repeat split; lia]] ].
  Qed.

  (* ---------------------------------------------------------------------------
   * The theorem
   * --------------------------------------------------------------------------- *)

  Theorem fdiv_flocq_holds : fdiv_flocq.
  Proof.
    intros rm a b. rewrite fdiv_core_res, fdiv_core_flags.
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    destruct (classify a sa Ea Ma HMa HEa Ha) as (Sga & SNa & Ca).
    destruct (classify b sb Eb Mb HMb HEb Hb) as (Sgb & SNb & Cb).
    cbv beta in Sga, SNa, Ca, Sgb, SNb, Cb.
    unfold divV, divFlags. cbv beta zeta. rewrite Sga, Sgb, SNa, SNb.
    destruct Ca as [(Ta & Za & Ia & Na & Pa) | [(Ta & Za & Ia & Na & Pa) | [(Ta & Za & Ia & Na) |
                    ((ma & exa & Hba & Ta) & Za & Ia & Na & Pa & Hna & Hza)]]];
    destruct Cb as [(Tb & Zb & Ib & Nb & Pb) | [(Tb & Zb & Ib & Nb & Pb) | [(Tb & Zb & Ib & Nb) |
                    ((mb & exb & Hbb & Tb) & Zb & Ib & Nb & Pb & Hnb & Hzb)]]];
    rewrite Za, Ia, Na, Zb, Ib, Nb; cbn [orb andb negb].
    16: {
      pose proof (fin_facts e f Hf Hpe a sa Ea Ma HMa HEa Ha Hna Hza) as FA.
      pose proof (fin_facts e f Hf Hpe b sb Eb Mb HMb HEb Hb Hnb Hzb) as FB.
      cbv beta zeta in FA, FB.
      destruct FA as (FSa & FXa & FVa & FFa & FSga). destruct FB as (FSb & FXb & FVb & FFb & FSgb).
      destruct (div_fin_core rm (toB a) (toB b) sa sb _ _ _ _ FSa FSb FXa FXb FVa FVb FFa FSga FSgb) as [R F].
      split; [exact R | rewrite F, Ta, Tb; reflexivity]. }
    all: rewrite Ta, Tb; cbn [BinarySingleNaN.Bdiv]; try rewrite Pa; try rewrite Pb; cbn [orb andb negb];
      rewrite ?orb_false_r, ?mkFlags_eval, ?(ofB_nan e f Hf Hpe), ?(ofB_inf e f Hf Hpe), ?(ofB_zero e f Hf Hpe);
      split; reflexivity.
  Qed.
End Div.
