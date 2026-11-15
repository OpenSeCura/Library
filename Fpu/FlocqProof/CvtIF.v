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
 * FCVT.fmt.{W,WU,L,LU} (integer -> floating point) against Flocq (`CvtIF.v`).
 *
 * `cvtIFRef rm u w x` is the reference core (`FpCoreRef.fpuComputeRef`) on a decoded FCVT from the
 * integer register `x` (`u`: unsigned, `w`: wide = all `xlen` bits, else the low `wlen` bits).
 * `cvtIF_flocq_holds`: its result is Flocq's `binary_normalize` of the integer `intOf u w x`
 * (exponent 0, sign of zero +) and its flags are the IEEE flags of rounding that integer.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Lemma testbit_top : forall v N, 1 <= N -> 0 <= v < 2 ^ N -> Z.testbit v (N - 1) = (2 ^ (N - 1) <=? v).
Proof.
  intros v N HN Hv.
  assert (HP : 2 ^ N = 2 * 2 ^ (N - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  pose proof (Z.testbit_spec' v (N - 1) ltac:(lia)) as H.
  destruct (Z.leb_spec (2 ^ (N - 1)) v).
  - rewrite <- (Z.div_unique v (2 ^ (N - 1)) 1 (v - 2 ^ (N - 1))) in H by lia.
    destruct (Z.testbit v (N - 1)); [reflexivity | discriminate H].
  - rewrite Z.div_small in H by lia. destruct (Z.testbit v (N - 1)); [discriminate H | reflexivity].
Qed.

Lemma neg_eval : forall w (a : Expr type (Bit w)), 0 <= w ->
  Zmod.unsigned (evalExpr (Neg a)) = (- Zmod.unsigned (evalExpr a)) mod 2 ^ w.
Proof.
  intros w a Hw. cbn [Neg evalExpr fold_left map].
  change (evalNot (k := Bit w) (evalExpr a)) with (Zmod.not (evalExpr a)).
  rewrite Zmod.add_0_l, Zmod.unsigned_add, bits.unsigned_not', Zmod.unsigned_1, Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia).
  rewrite Z.ones_equiv. replace (Z.pred (2 ^ w) - Zmod.unsigned (evalExpr a) + 1) with (- Zmod.unsigned (evalExpr a) + 1 * 2 ^ w) by lia.
  apply Z.mod_add; apply Z.pow_nonzero; lia.
Qed.

(* `(a mod 2^m) mod 2^n = a mod 2^n` for `n <= m`. *)
Lemma mod_pow2_mod : forall a n m, 0 <= n <= m -> (a mod 2 ^ m) mod 2 ^ n = a mod 2 ^ n.
Proof.
  intros a n m Hnm.
  replace (2 ^ m) with (2 ^ n * 2 ^ (m - n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  rewrite (Z.mul_comm (2 ^ n)), Z.mod_add by (apply Z.pow_nonzero; lia). apply Z.mod_mod; apply Z.pow_nonzero; lia.
Qed.

Section IntToFp.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).
  Hypothesis Hwl : 1 <= wlen <= xlen.
  (* The existing Fpu width condition (`FpCoreRef.v`). *)
  Hypothesis Hxl : xlen + 4 <= 7 * 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).

  Lemma Hxe : xlen + f + 3 < 2 ^ (e + 2).
  Proof. replace (e + 2) with ((e - 1) + 3) by (pose proof (He e f Hf Hpe); lia). rewrite Z.pow_add_r by (pose proof (He e f Hf Hpe); lia). lia. Qed.

  Local Instance precGt : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  Definition opIF (u w : bool) : type FpOpDK :=
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (true ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (u ,, (w ,, (false ,, tt)))))))))))))))))))))).

  Definition reqIF (u w : bool) (rm : bits 3) (x : bits xlen) : type (FpReqK e f xlen) :=
    (opIF u w ,, (rm ,, (Zmod.zero ,, (Zmod.zero ,, (Zmod.zero ,, (x ,, tt)))))).

  Definition cvtIFRef (rm : bits 3) (u w : bool) (x : bits xlen) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqIF u w rm x)).

  (* The integer operand: the low `wlen` bits (`w = false`) or all `xlen` bits, unsigned (`u`) or
   * two's complement. *)
  Definition intOf (u w : bool) (x : bits xlen) : Z :=
    let N := if w then xlen else wlen in
    let v := Zmod.to_Z x mod 2 ^ N in
    if u then v else if Z.testbit v (N - 1) then v - 2 ^ N else v.

  Lemma cvtIF_core_res : forall rm u w x,
    (cvtIFRef rm u w x) @% "res" = (evalLetExpr (intToFp false e f xlen wlen type rm (negb u) w x)).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma cvtIF_core_flags : forall rm u w x,
    (cvtIFRef rm u w x) @% "flags" = (evalLetExpr (intToFp false e f xlen wlen type rm (negb u) w x)).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma intOf_cases : forall (u w : bool) (x : bits xlen), let N := if w then xlen else wlen in let v := Zmod.to_Z x mod 2 ^ N in
    1 <= N <= xlen /\ 0 <= v < 2 ^ N /\ Z.testbit v (N - 1) = Z.testbit (Zmod.to_Z x) (N - 1) /\
    intOf u w x = (if negb u && (2 ^ (N - 1) <=? v) then v - 2 ^ N else v).
  Proof.
    intros u w x N v.
    assert (HN : 1 <= N <= xlen) by (unfold N; destruct w; lia).
    assert (Hv : 0 <= v < 2 ^ N) by (apply Z.mod_pos_bound; lia).
    split; [exact HN |]; split; [exact Hv |]; split; [apply Z.mod_pow2_bits_low; lia |].
    unfold intOf; fold N v. rewrite testbit_top by lia. destruct u; reflexivity.
  Qed.

  Lemma intToFp_eval : forall rm u w x, let n := intOf u w x in
    evalLetExpr (intToFp false e f xlen wlen type rm (negb u) w x) =
    evalLetExpr (normRound false e f type (xlen + f + 3) (n <? 0) (Zmod.of_Z _ (xlen - 1))
                   (Zmod.of_Z _ (Z.abs n * 2 ^ (f + 3))) false rm).
  Proof.
    intros rm u w x n.
    destruct (intOf_cases u w x) as (HN & Hv & Htv & Hn); cbv zeta in HN, Hv, Htv, Hn.
    set (N := if w then xlen else wlen) in *. set (v := Zmod.to_Z x mod 2 ^ N) in *.
    fold n in Hn.
    assert (Hvd : v = Zmod.to_Z x mod 2 ^ N) by reflexivity. clearbody v.
    assert (HNw : N = if w then xlen else wlen) by reflexivity. clearbody N.
    unfold intToFp; cbn [evalLetExpr].
    match goal with |- evalLetExpr (normRound _ _ _ _ _ ?A ?B ?C ?D _) = _ =>
      set (Av := A); set (Bv := B); set (Cv := C) end.
    assert (HB : Bv = Zmod.of_Z _ (xlen - 1)) by (unfold Bv; cbn [evalExpr cst expOff]; rewrite Z.add_0_r; reflexivity).
    assert (HP : 2 ^ N = 2 * 2 ^ (N - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (HA : Av = (n <? 0)).
    { unfold Av. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault].
      rewrite !bitSet_testbit by lia.
      destruct w; cbv iota in HNw |- *; [replace (xlen - 1) with (N - 1) by lia | replace (wlen - 1) with (N - 1) by lia].
      all: rewrite <- Htv, testbit_top, Hn by lia.
      all: destruct u; cbn [andb negb]; [symmetry; apply Z.ltb_ge; lia |].
      all: destruct (Z.leb_spec (2 ^ (N - 1)) v); [symmetry; apply Z.ltb_lt; lia | symmetry; apply Z.ltb_ge; lia]. }
    assert (HC : Cv = Zmod.of_Z _ (Z.abs n * 2 ^ (f + 3))).
    { unfold Cv. apply Zmod.unsigned_inj. cbn [evalExpr].
      rewrite bits.unsigned_slu, unsigned_zext by lia.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd].
      rewrite !bitSet_testbit by lia.
      rewrite unsigned_cst by lia.
      destruct w; cbv iota in HNw |- *; [replace (xlen - 1) with (N - 1) by lia | replace (wlen - 1) with (N - 1) by lia].
      all: rewrite <- Htv, testbit_top by lia.
      all: rewrite unsigned_and_m1_l by lia; rewrite bits.unsigned_and, unsigned_cst by lia.
      all: assert (Hx2 : 2 ^ wlen <= 2 ^ xlen) by (apply Z.pow_le_mono_r; lia).
      1: replace (-1 mod 2 ^ xlen) with (Z.ones N) by (rewrite Z.ones_equiv, HNw; apply Z.mod_unique with (-1); lia).
      2: replace ((2 ^ wlen - 1) mod 2 ^ xlen) with (Z.ones N) by (rewrite Z.ones_equiv, HNw, Z.mod_small by lia; lia).
      all: rewrite Z.land_ones by lia.
      all: assert (HW : 2 ^ (xlen + f + 3) = 2 ^ xlen * 2 ^ (f + 3)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      all: assert (Hf3 : f + 3 < 2 ^ (xlen + f + 3)) by (pose proof (Z.pow_gt_lin_r 2 (f + 3) ltac:(lia) ltac:(lia));
             assert (2 ^ (f + 3) <= 2 ^ (xlen + f + 3)) by (apply Z.pow_le_mono_r; lia); lia).
      all: rewrite (Z.mod_small (f + 3)), Z.shiftl_mul_pow2 by lia.
      all: assert (HNx : 2 ^ N <= 2 ^ xlen) by (apply Z.pow_le_mono_r; lia).
      all: assert (Hn2 : 0 <= Z.abs n < 2 ^ N) by (rewrite Hn; destruct u; cbn [andb negb]; [| destruct (Z.leb_spec (2 ^ (N - 1)) v)]; cbv iota; lia).
      all: assert (Hp3 : 0 < 2 ^ (f + 3)) by (apply Z.pow_pos_nonneg; lia).
      all: assert (Hb : 0 <= Z.abs n * 2 ^ (f + 3) < 2 ^ (xlen + f + 3))
             by (rewrite HW; split; [lia | apply Z.mul_lt_mono_pos_r; lia]).
      all: rewrite tz_ofZ by lia.
      all: cbn [InvDefault]; rewrite Hn in Hb |- *.
      all: destruct u; cbn [andb negb] in Hb |- *; [| destruct (Z.leb_spec (2 ^ (N - 1)) v)]; cbv iota in Hb |- *.
      1: (match goal with |- context [Zmod.unsigned ?y mod 2 ^ N] =>
                  replace (Zmod.unsigned y mod 2 ^ N) with v by (rewrite Hvd; reflexivity) end;
                rewrite Z.abs_eq in Hb |- * by lia; apply Z.mod_small; lia).
      2: (match goal with |- context [Zmod.unsigned ?y mod 2 ^ N] =>
                  replace (Zmod.unsigned y mod 2 ^ N) with v by (rewrite Hvd; reflexivity) end;
                rewrite Z.abs_eq in Hb |- * by lia; apply Z.mod_small; lia).
      2: (match goal with |- context [Zmod.unsigned ?y mod 2 ^ N] =>
                  replace (Zmod.unsigned y mod 2 ^ N) with v by (rewrite Hvd; reflexivity) end;
                rewrite Z.abs_eq in Hb |- * by lia; apply Z.mod_small; lia).
      3: (match goal with |- context [Zmod.unsigned ?y mod 2 ^ N] =>
                  replace (Zmod.unsigned y mod 2 ^ N) with v by (rewrite Hvd; reflexivity) end;
                rewrite Z.abs_eq in Hb |- * by lia; apply Z.mod_small; lia).
      all: match goal with |- context [Zmod.unsigned (evalExpr (Neg ?a))] =>
             replace (Zmod.unsigned (evalExpr (Neg a))) with ((- Zmod.unsigned x) mod 2 ^ xlen)
               by (symmetry; exact (neg_eval _ a ltac:(lia))) end.
      all: rewrite mod_pow2_mod, Z.mod_opp_l_nz, <- Hvd by (try apply Z.pow_nonzero; lia).
      all: rewrite Z.abs_neq in Hb |- * by lia; rewrite Z.mod_small by lia; lia. }
    match goal with |- evalLetExpr (normRound _ _ _ _ _ _ _ ?C _ _) = _ => change C with Cv end.
    rewrite HA, HB, HC; reflexivity.
  Qed.

  Lemma intOf_abs : forall u w x, Z.abs (intOf u w x) < 2 ^ xlen.
  Proof.
    intros u w x.
    destruct (intOf_cases u w x) as (HN & Hv & _ & Hn); cbv zeta in HN, Hv, Hn.
    set (N := if w then xlen else wlen) in *. set (v := Zmod.to_Z x mod 2 ^ N) in *.
    clearbody N v.
    assert (HP : 2 ^ N = 2 * 2 ^ (N - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (HNx : 2 ^ N <= 2 ^ xlen) by (apply Z.pow_le_mono_r; lia).
    rewrite Hn; destruct u; cbn [andb negb]; [| destruct (Z.leb_spec (2 ^ (N - 1)) v)]; cbv iota; lia.
  Qed.

  Lemma HeC : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Lemma normRound_zero : forall Wd s x (wsig : bits Wd) rm, Zmod.to_Z wsig = 0 ->
    evalLetExpr (normRound false e f type Wd s x wsig false rm) =
    (evalExpr (zeroE e f type (ConstBool s)) ,, (Zmod.of_Z _ 0 ,, tt)).
  Proof.
    intros Wd s x wsig rm Hw. unfold normRound; cbn [evalLetExpr].
    cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault evalNot].
    rewrite isZero_eval, Hw. exact eq_refl.
  Qed.

  Lemma flags_0 : forall m, finiteFlags (f + 1) (2 ^ (e - 1)) m 0%R = Zmod.of_Z _ 0.
  Proof.
    intros m. unfold finiteFlags, roundFlags. rewrite !round_0 by apply valid_rnd_round_mode.
    rewrite Rabs_R0, Rlt_bool_true by apply bpow_gt_0. rewrite Req_bool_true by reflexivity. destruct (Rlt_bool _ _); reflexivity.
  Qed.

  Lemma Rlt_bool_IZR : forall n, Rlt_bool (IZR n) 0 = (n <? 0).
  Proof.
    intros n; destruct (Rlt_bool_spec (IZR n) 0) as [H | H]; destruct (Z.ltb_spec n 0) as [H' | H']; try reflexivity.
    - apply lt_IZR in H; lia.
    - apply IZR_lt in H'; lra.
  Qed.

  Lemma Rcompare_IZR : forall n, n <> 0 ->
    match Rcompare (IZR n) 0 with Datatypes.Eq => false | Lt => true | Gt => false end = (n <? 0).
  Proof.
    intros n Hn; destruct (Z.ltb_spec n 0) as [H | H].
    - rewrite Rcompare_Lt by (apply IZR_lt; exact H); reflexivity.
    - rewrite Rcompare_Gt by (apply IZR_lt; lia); reflexivity.
  Qed.

  Lemma B2SF_overflow_nan : forall m s (b : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))),
    BinarySingleNaN.B2SF b = BinarySingleNaN.binary_overflow (f + 1) (2 ^ (e - 1)) m s -> BinarySingleNaN.is_nan b = false.
  Proof.
    intros m s b H; destruct b; try reflexivity. cbn in H. unfold BinarySingleNaN.binary_overflow in H.
    destruct (BinarySingleNaN.overflow_to_inf m s); discriminate H.
  Qed.

  (* FCVT.fmt.{W,WU,L,LU}: Flocq's `binary_normalize` of the integer (exponent 0, zero sign +). *)
  Definition cvtIF_flocq : Prop :=
    forall rm u w x,
      (cvtIFRef rm u w x) @% "res" =
        ofB (BinarySingleNaN.binary_normalize (f + 1) (2 ^ (e - 1)) precGt precLt (modeOf rm) (intOf u w x) 0 false) /\
      (cvtIFRef rm u w x) @% "flags" = finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) (IZR (intOf u w x)).

  Theorem cvtIF_flocq_holds : cvtIF_flocq.
  Proof.
    intros rm u w x.
    rewrite cvtIF_core_res, cvtIF_core_flags, intToFp_eval; cbv zeta.
    pose proof (intOf_abs u w x) as Hab.
    set (n := intOf u w x) in *. clearbody n.
    pose proof HeC as He2.
    assert (P8 : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (HW : 2 ^ (xlen + f + 3) = 2 ^ xlen * 2 ^ (f + 3)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hp3 : 0 < 2 ^ (f + 3)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hb : 0 <= Z.abs n * 2 ^ (f + 3) < 2 ^ (xlen + f + 3))
      by (rewrite HW; split; [lia | apply Z.mul_lt_mono_pos_r; lia]).
    destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
    - subst n. rewrite normRound_zero by (rewrite tz_ofZ by lia; reflexivity). cbn [Fst Snd]. split.
      + change (BinarySingleNaN.binary_normalize (f + 1) (2 ^ (e - 1)) precGt precLt (modeOf rm) 0 0 false)
          with (@BinarySingleNaN.B754_zero (f + 1) (2 ^ (e - 1)) false).
        rewrite (ofB_zero e f Hf Hpe); reflexivity.
      + rewrite flags_0; reflexivity.
    - assert (Hw0 : 0 < Zmod.to_Z (Zmod.of_Z (2 ^ (xlen + f + 3)) (Z.abs n * 2 ^ (f + 3))))
        by (rewrite tz_ofZ by lia; apply Z.mul_pos_pos; lia).
      assert (Hx1 : Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) (xlen - 1)) = xlen - 1) by (apply signed_k; lia).
      pose proof (normRound_eval e f He2 Hf (xlen + f + 3) (n <? 0) (Zmod.of_Z _ (xlen - 1))
                    (Zmod.of_Z _ (Z.abs n * 2 ^ (f + 3))) false rm ltac:(lia) Hxe Hw0 ltac:(rewrite Hx1; lia)) as HR.
      cbv zeta in HR; rewrite HR; clear HR.
      rewrite Hx1, tz_ofZ by lia.
      set (Wv := Z.abs n * 2 ^ (f + 3)) in *.
      set (k := xlen + f + 3 - 1 - Z.log2 Wv).
      set (d := xlen + f + 3 - (f + 3)).
      destruct (norm_window f Hf (xlen + f + 3) Wv ltac:(lia) ltac:(lia)) as (Hk & HN & HS); fold k d in Hk, HN, HS.
      assert (Hin : inbetween_float radix2 Wv (xlen - 1 - (xlen + f + 3 - 1)) (Rabs (IZR n)) loc_Exact).
      { constructor. rewrite <- abs_IZR. replace (xlen - 1 - (xlen + f + 3 - 1)) with (0 - (f + 3)) by lia.
        unfold Wv; rewrite F2R_scale by lia. rewrite F2R_eq; simpl bpow; ring. }
      destruct (norm_loc f Hf (xlen + f + 3) Wv (xlen - 1) false (IZR n) loc_Exact ltac:(lia) ltac:(lia) Hin
                  ltac:(split; reflexivity) ltac:(discriminate)) as (l2 & Hin2 & Hl2); fold k d in Hin2, Hl2.
      rewrite (roundPack_Z e f He2 Hf Hpe). cbn [Fst Snd].
      rewrite signed_k by lia. rewrite tz_ofZ by lia.
      assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)); change (2 ^ 3) with 8 in *; lia).
      pose proof (BinarySingleNaN.binary_normalize_correct (f + 1) (2 ^ (e - 1)) precGt precLt (modeOf rm) n 0 false) as HN0.
      cbv zeta in HN0.
      replace (F2R (Float radix2 n 0)) with (IZR n) in HN0 by (rewrite F2R_eq; simpl bpow; ring).
      rewrite Rcompare_IZR, Rlt_bool_IZR in HN0 by exact Hn0.
      split.
      + set (bn := BinarySingleNaN.binary_normalize (f + 1) (2 ^ (e - 1)) precGt precLt (modeOf rm) n 0 false) in *.
        assert (Hbn : toB (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) (n <? 0) (xlen - 1 - k) (Wv * 2 ^ k / 2 ^ d)
                                         (false || negb ((Wv * 2 ^ k) mod 2 ^ d =? 0)))) = bn).
        { apply (rp_result e f Hf Hpe _ _ _ _ _ (IZR n) l2 Hrm HS Hin2 Hl2 (Rlt_bool_IZR n)). exact HN0. }
        rewrite <- Hbn, ofB_toB; [reflexivity |]. rewrite Hbn.
        destruct (Rlt_bool _ _) in HN0.
        * destruct HN0 as (_ & Hfin & _). destruct bn; try reflexivity; discriminate Hfin.
        * exact (B2SF_overflow_nan _ _ _ HN0).
      + unfold finiteFlags. change (modeOf rm) with (modeZ (Zmod.to_Z rm)).
        rewrite (rp_flags e f Hf Hpe _ _ _ _ _ (IZR n) l2 Hrm HS Hin2 Hl2 (Rlt_bool_IZR n)). reflexivity.
  Qed.
End IntToFp.

