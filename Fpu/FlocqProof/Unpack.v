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
 * `FpCore.fpUnpack` (reference mode) against the field split (`Unpack.v`).
 *
 * For `a` with sign `s`, exponent field `E` and fraction field `M`, the unpacked record has the
 * class flags of `(E, M)`, and for a finite non-zero `a` a normalized significand `Sg` (top bit `f`)
 * and unbiased exponent `X` with `Sg * 2^(X - f)` the value of the fields (`unpack_value`).
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Reals.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Flags RoundBits NormRound.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma isZero_eval : forall w (x : bits w), evalExpr (isZero (Var type (Bit w) x)) = (Zmod.to_Z x =? 0).
Proof.
  intros w x; cbn [evalExpr isZero isEq KindCustomInd getDefault].
  destruct (Zmod.eqb_spec x Zmod.zero) as [-> | Hn]; [rewrite Zmod.unsigned_0; reflexivity |].
  symmetry; apply Z.eqb_neq; intros H; apply Hn, Zmod.unsigned_inj; rewrite H, Zmod.unsigned_0; reflexivity.
Qed.

Lemma isAllOnes_eval : forall w (x : bits w), 0 <= w ->
  evalExpr (isAllOnes (Var type (Bit w) x)) = (Zmod.to_Z x =? 2 ^ w - 1).
Proof.
  intros w x Hw; cbn [evalExpr isAllOnes isEq KindCustomInd InvDefault].
  assert (Hm : Zmod.to_Z (Zmod.of_Z (2 ^ w) (-1)) = 2 ^ w - 1).
  { rewrite Zmod.unsigned_of_Z; symmetry; apply Z.mod_unique with (-1); pose proof (Z.pow_pos_nonneg 2 w); lia. }
  destruct (Zmod.eqb_spec x (Zmod.of_Z (2 ^ w) (-1))) as [-> | Hn]; [rewrite Hm, Z.eqb_refl; reflexivity |].
  symmetry; apply Z.eqb_neq; intros H; apply Hn, Zmod.unsigned_inj; rewrite H, Hm; reflexivity.
Qed.

Lemma lastn_eval : forall n w (a : bits w), 0 <= n <= w ->
  Zmod.to_Z (Zmod_lastn n a) = Zmod.to_Z a / 2 ^ (w - n).
Proof.
  intros n w a Hn; unfold Zmod_lastn.
  rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by lia.
  pose proof (bits.unsigned_range a ltac:(lia)).
  apply Z.mod_small; split; [apply Z.div_pos; lia |].
  apply Z.div_lt_upper_bound; [lia |]. rewrite <- Z.pow_add_r by lia. replace (2 ^ (w - n + n)) with (2 ^ w) by (f_equal; lia). lia.
Qed.

Lemma F2R_scale : forall m k x, 0 <= k -> F2R (Float radix2 (m * 2 ^ k) (x - k)) = F2R (Float radix2 m x).
Proof.
  intros m k x Hk; unfold F2R; cbn [Fnum Fexp].
  rewrite mult_IZR, <- bpow_2_R by exact Hk. rewrite Rmult_assoc, <- bpow_plus. f_equal; f_equal; lia.
Qed.

Section Unpack.
  Variable e f : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Variable a : bits (f + e + 1).
  Variables (s : bool) (E M : Z).
  Hypothesis HM : 0 <= M < 2 ^ f.
  Hypothesis HE : 0 <= E < 2 ^ e.
  Hypothesis Ha : Zmod.to_Z a = b2z s * 2 ^ (f + e) + E * 2 ^ f + M.

  Local Abbreviation u := (evalLetExpr (fpUnpack false e f type a)).

  Lemma pfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e.
  Proof. apply Z.pow_add_r; lia. Qed.

  Lemma Hmag : Zmod.to_Z (Zmod.firstn (f + e) a) = E * 2 ^ f + M.
  Proof.
    rewrite bits.unsigned_firstn, Ha. pose proof pfe. assert (0 <= E * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia).
    replace (b2z s * 2 ^ (f + e) + E * 2 ^ f + M) with (E * 2 ^ f + M + b2z s * 2 ^ (f + e)) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. split; [lia |].
    assert (E * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  Qed.

  Lemma Hef : Zmod.to_Z (Zmod_lastn e (Zmod.firstn (f + e) a)) = E.
  Proof.
    rewrite lastn_eval by lia. rewrite Hmag. replace (f + e - e) with f by lia.
    symmetry; apply Z.div_unique with M; lia.
  Qed.

  Lemma Hfr : Zmod.to_Z (Zmod.firstn f (Zmod.firstn (f + e) a)) = M.
  Proof.
    rewrite bits.unsigned_firstn, Hmag. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small; lia.
  Qed.

  Lemma u_sign : u.(Fst) = s.
  Proof.
    unfold fpUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd].
    rewrite evalExpr_isNotZero_bits; cbn [evalExpr].
    rewrite lastn_eval by lia. rewrite Ha. replace (f + e + 1 - 1) with (f + e) by lia.
    pose proof pfe. assert (0 <= E * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia).
    assert (E * 2 ^ f + M < 2 ^ (f + e)) by (assert (E * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
    rewrite <- (Z.div_unique (b2z s * 2 ^ (f + e) + E * 2 ^ f + M) (2 ^ (f + e)) (b2z s) (E * 2 ^ f + M)) by lia.
    destruct s; reflexivity.
  Qed.

  Lemma u_zero : u.(Snd).(Fst) = (E =? 0) && (M =? 0).
  Proof.
    unfold fpUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd fold_left map evalAndBinary evalBinary KindCustomInd InvDefault].
    rewrite !isZero_eval, Hef, Hfr; reflexivity.
  Qed.

  Lemma u_inf : u.(Snd).(Snd).(Fst) = (E =? 2 ^ e - 1) && (M =? 0).
  Proof.
    unfold fpUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd fold_left map evalAndBinary evalBinary KindCustomInd InvDefault].
    rewrite isAllOnes_eval, isZero_eval, Hef, Hfr by lia; reflexivity.
  Qed.

  Lemma u_nan : u.(Snd).(Snd).(Snd).(Fst) = (E =? 2 ^ e - 1) && negb (M =? 0).
  Proof.
    unfold fpUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd fold_left map evalAndBinary evalBinary KindCustomInd InvDefault].
    rewrite isAllOnes_eval, isZero_eval, Hef, Hfr by lia; reflexivity.
  Qed.

  Lemma u_snan : u.(Snd).(Snd).(Snd).(Snd).(Fst) =
                 (E =? 2 ^ e - 1) && negb (M =? 0) && negb (Z.testbit M (f - 1)).
  Proof.
    unfold fpUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd fold_left map evalAndBinary evalBinary KindCustomInd InvDefault].
    rewrite isAllOnes_eval, isZero_eval, bitSet_testbit, Hef, Hfr by lia; reflexivity.
  Qed.

  Local Abbreviation rawv := (M + b2z (negb (E =? 0)) * 2 ^ f).
  Local Abbreviation kv := (f - Z.log2 rawv).

  Lemma raw_pos : (E <> 0 \/ M <> 0) -> 0 < rawv < 2 ^ (f + 1).
  Proof.
    intros H; assert (2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    destruct (Z.eqb_spec E 0); cbn [negb b2z]; lia.
  Qed.

  Lemma kv_range : (E <> 0 \/ M <> 0) -> 0 <= kv <= f /\ 2 ^ f <= rawv * 2 ^ kv < 2 ^ (f + 1).
  Proof.
    intros H; pose proof (raw_pos H) as Hr.
    pose proof (norm_window f Hf (f + 4) rawv ltac:(lia)) as _.
    pose proof (Z.log2_spec rawv ltac:(lia)) as HL.
    assert (HL2 : Z.log2 rawv < f + 1) by (apply Z.log2_lt_pow2; lia).
    assert (Hk : 0 <= kv <= f) by (pose proof (Z.log2_nonneg rawv); lia).
    split; [exact Hk |].
    assert (0 < 2 ^ kv) by (apply Z.pow_pos_nonneg; lia).
    split.
    - replace f with (Z.log2 rawv + kv) at 1 by lia. rewrite Z.pow_add_r by lia. apply Z.mul_le_mono_nonneg_r; lia.
    - replace (2 ^ (f + 1)) with (2 ^ Z.succ (Z.log2 rawv) * 2 ^ kv) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      apply Z.mul_lt_mono_pos_r; lia.
  Qed.

  Lemma u_sig : (E <> 0 \/ M <> 0) ->
    u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) = Zmod.of_Z _ (rawv * 2 ^ kv).
  Proof.
    intros H; pose proof (raw_pos H) as Hr; destruct (kv_range H) as [Hk Hn].
    unfold fpUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd].
    rewrite isZero_eval, Hef.
    match goal with |- context [evalExpr (clz (f + 1) (e + 3) ?r)] => set (rawZ := r) end.
    assert (Hraw : Zmod.to_Z rawZ = rawv).
    { unfold rawZ; cbn [evalExpr boolBit evalNot]. rewrite unsigned_app_arith by lia. rewrite Hfr.
      destruct (E =? 0); cbn; lia. }
    clearbody rawZ.
    rewrite (clz_eval (f + 1) (e + 3) rawZ ltac:(lia) ltac:(lia)), Hraw.
    replace (f + 1 - 1 - Z.log2 rawv) with kv by lia.
    cbn [fold_left map evalOrBinary evalBinary KindCustomInd getDefault cst evalExpr].
    assert (He3 : f < 2 ^ (e + 3)) by (assert (2 ^ (e - 1) <= 2 ^ (e + 3)) by (apply Z.pow_le_mono_r; lia); lia).
    apply Zmod.unsigned_inj. rewrite !bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l, bits.unsigned_slu.
    rewrite (tz_ofZ (e + 3) kv) by lia. rewrite Hraw, Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (rawv * 2 ^ kv)) by lia.
    assert (2 ^ f < 2 ^ (f + 1)) by (apply Z.pow_lt_mono_r; lia).
    rewrite (tz_ofZ (f + 1) (2 ^ f)), (tz_ofZ (f + 1) (rawv * 2 ^ kv)) by lia.
    apply Z.bits_inj'; intros i Hi. rewrite Z.lor_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec f i) as [<- | _]; [| apply orb_false_r]. rewrite orb_true_r.
    symmetry; apply Z.testbit_true; [lia |].
    assert (2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia). rewrite <- (Z.div_unique (rawv * 2 ^ kv) (2 ^ f) 1 (rawv * 2 ^ kv - 2 ^ f)) by lia. reflexivity.
  Qed.

  Lemma u_exp : (E <> 0 \/ M <> 0) ->
    u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) = Zmod.of_Z _ ((if E =? 0 then 1 else E) - fpBias e - kv).
  Proof.
    intros H; pose proof (raw_pos H) as Hr; destruct (kv_range H) as [Hk Hn].
    unfold fpUnpack, expUnpack; cbn [evalLetExpr]; cbn [Fst Snd evalExpr mapDiffTuple snd].
    rewrite isZero_eval, Hef.
    match goal with |- context [evalExpr (clz (f + 1) (e + 3) ?r)] => set (rawZ := r) end.
    assert (Hraw : Zmod.to_Z rawZ = rawv).
    { unfold rawZ; cbn [evalExpr boolBit evalNot]. rewrite unsigned_app_arith by lia. rewrite Hfr.
      destruct (E =? 0); cbn; lia. }
    clearbody rawZ.
    rewrite (clz_eval (f + 1) (e + 3) rawZ ltac:(lia) ltac:(lia)), Hraw.
    replace (f + 1 - 1 - Z.log2 rawv) with kv by lia.
    rewrite !(sub_eval (e + 3) ltac:(lia)). cbn [evalExpr cst].
    assert (He3 : 2 ^ e < 2 ^ (e + 3)) by (apply Z.pow_lt_mono_r; lia).
    match goal with |- Zmod.sub (Zmod.sub ?eb _) _ = _ =>
      assert (Heb : eb = Zmod.of_Z (2 ^ (e + 3)) (if E =? 0 then 1 else E)); [| rewrite Heb] end.
    { destruct (E =? 0); [reflexivity |].
      apply Zmod.unsigned_inj; rewrite unsigned_ZeroExtend by lia; cbn [evalExpr]; rewrite Hef, tz_ofZ by lia; reflexivity. }
    rewrite <- !Zmod.of_Z_sub; reflexivity.
  Qed.

  Lemma u_value : E <> 2 ^ e - 1 -> (E <> 0 \/ M <> 0) ->
    let X := Zmod.signed u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) in
    let Sg := Zmod.to_Z u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) in
    2 ^ f <= Sg < 2 ^ (f + 1) /\ fpEmin e - f <= X <= fpEmax e /\
    F2R (Float radix2 Sg (X - f)) =
    F2R (Float radix2 (if E =? 0 then M else M + 2 ^ f)
                      (if E =? 0 then SpecFloat.emin (f + 1) (2 ^ (e - 1)) else E + SpecFloat.emin (f + 1) (2 ^ (e - 1)) - 1)).
  Proof.
    intros H1 H X Sg.
    pose proof (raw_pos H) as Hr; destruct (kv_range H) as [Hk Hn].
    assert (HP : 2 ^ e = 2 * 2 ^ (e - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (HP8 : 2 ^ (e + 3 - 1) = 8 * 2 ^ (e - 1)) by (replace (e + 3 - 1) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (HX : X = (if E =? 0 then 1 else E) - fpBias e - kv).
    { unfold X; rewrite (u_exp H). apply signed_of_Z_small; [lia |]. rewrite HP8.
      unfold fpBias; destruct (E =? 0); lia. }
    assert (HS : Sg = rawv * 2 ^ kv).
    { unfold Sg; rewrite (u_sig H). apply tz_ofZ; lia. }
    rewrite HX, HS; clear HX HS X Sg.
    split; [exact Hn |].
    unfold fpEmin, fpEmax, fpBias, SpecFloat.emin.
    destruct (Z.eqb_spec E 0) as [E0 | E0]; cbn [negb b2z] in *.
    - split; [lia |]. rewrite Z.mul_0_l, Z.add_0_r in *.
      set (k := f - Z.log2 M) in *.
      replace (1 - (2 ^ (e - 1) - 1) - k - f) with ((2 - 2 ^ (e - 1) - f) - k) by lia.
      rewrite F2R_scale by lia. f_equal; f_equal; lia.
    - assert (Hlog : Z.log2 (M + 1 * 2 ^ f) = f) by (apply Z.log2_unique; [lia |]; rewrite Z.pow_succ_r by lia; lia).
      rewrite Hlog, Z.sub_diag, Z.pow_0_r, Z.mul_1_r, Z.mul_1_l. split; [lia |]. f_equal; f_equal; lia.
  Qed.
End Unpack.
