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
 * FCVT.{W,WU,L,LU}.fmt (floating point -> integer) against a Flocq-based spec (`CvtFI.v`).
 *
 * Flocq has no float-to-integer conversion with saturation, so `fiSpec` writes the RISC-V rule
 * with Flocq: `n := round_mode (modeOf rm) (B2R a)` (Flocq's rounding of the real value to an
 * integer); if `n` is in the integer range `[loZ u w, hiZ u w]` the result is `n` with NX when
 * `IZR n <> B2R a`, else the saturated bound of the operand's sign with NV; NaN gives the maximum
 * with NV, infinities the bound of their sign with NV, zeros 0.  `wlen`-bit results are sign-extended
 * to XLEN (`encZ`).  `cvtFI_flocq_holds`: the reference core (`fpuComputeRef`) computes `fiSpec`.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul CvtIF CvtRound CvtFF.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Lemma lor_add : forall a b, Z.land a b = 0 -> Z.lor a b = a + b.
Proof.
  intros a b H. rewrite Z.add_nocarry_lxor by exact H. apply Z.bits_inj'; intros i Hi.
  rewrite Z.lor_spec, Z.lxor_spec. pose proof (f_equal (fun z => Z.testbit z i) H) as H'; cbn beta in H'.
  rewrite Z.land_spec, Z.bits_0 in H'. destruct (Z.testbit a i), (Z.testbit b i); try discriminate H'; reflexivity.
Qed.

Lemma land_low_high : forall t c k, 0 <= k -> 0 <= t < 2 ^ k -> 0 <= c -> Z.land t (c * 2 ^ k) = 0.
Proof.
  intros t c k Hk Ht Hc. apply Z.bits_inj'; intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small t (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The low `wl` bits, sign-extended. *)
Definition sextWZ (wl v : Z) : Z := let t := v mod 2 ^ wl in if t <? 2 ^ (wl - 1) then t else t - 2 ^ wl.

Lemma sextWZ_mod : forall wl v n, 0 <= wl <= n -> sextWZ wl (v mod 2 ^ n) = sextWZ wl v.
Proof. intros wl v n Hn; unfold sextWZ; rewrite mod_pow2_mod by lia; reflexivity. Qed.

Lemma sextW_eval : forall xlen wlen (x : bits xlen), 1 <= wlen <= xlen ->
  evalExpr (sextW xlen wlen type x) = Zmod.of_Z (2 ^ xlen) (sextWZ wlen (Zmod.to_Z x)).
Proof.
  intros xlen wlen x Hx. apply Zmod.unsigned_inj. unfold sextW.
  cbn [evalExpr fold_left map evalOrBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault].
  rewrite bitSet_testbit by lia. rewrite unsigned_and_m1_l by lia.
  rewrite !bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l, bits.unsigned_and.
  assert (Hwx : 2 ^ wlen <= 2 ^ xlen) by (apply Z.pow_le_mono_r; lia).
  assert (Hw2 : 2 ^ wlen = 2 * 2 ^ (wlen - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hw1 : 1 <= 2 ^ (wlen - 1)) by (pose proof (Z.pow_le_mono_r 2 0 (wlen - 1)); lia).
  cbn [evalExpr cst]. rewrite (tz_ofZ xlen (2 ^ wlen - 1)) by lia.
  replace (2 ^ wlen - 1) with (Z.ones wlen) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
  set (X := Zmod.to_Z x). set (t := X mod 2 ^ wlen).
  assert (Ht : 0 <= t < 2 ^ wlen) by (apply Z.mod_pos_bound; lia).
  replace (Z.testbit X (wlen - 1)) with (2 ^ (wlen - 1) <=? t)
    by (symmetry; rewrite <- (Z.mod_pow2_bits_low X wlen (wlen - 1)) by lia; unfold t;
        apply testbit_top; [lia | apply Z.mod_pos_bound; lia]).
  unfold sextWZ; fold t. rewrite Zmod.unsigned_of_Z.
  destruct (Z.leb_spec (2 ^ (wlen - 1)) t) as [Hb | Hb].
  - replace (t <? 2 ^ (wlen - 1)) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite tz_ofZ by lia. rewrite lor_add.
    + apply Z.mod_unique with (-1); lia.
    + replace (2 ^ xlen - 2 ^ wlen) with ((2 ^ (xlen - wlen) - 1) * 2 ^ wlen)
        by (rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia; replace (xlen - wlen + wlen) with xlen by lia; lia).
      apply land_low_high; lia.
  - replace (t <? 2 ^ (wlen - 1)) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite tz_ofZ, Z.lor_0_r by lia. symmetry; apply Z.mod_small; lia.
Qed.

Lemma mkFlags_evalV : forall nv nx,
  evalExpr (mkFlags type (Var type Bool nv) (ConstBool false) (ConstBool false) (ConstBool false) (Var type Bool nx)) =
  mkFl nv false false false nx.
Proof. intros [] []; vm_compute; reflexivity. Qed.

Lemma round_FIX0 : forall (rnd : R -> Z) {Hr : Valid_rnd rnd} x, round radix2 (FIX_exp 0) rnd x = IZR (rnd x).
Proof.
  intros rnd Hr x. unfold round, F2R, scaled_mantissa, cexp, FIX_exp. cbn [Fnum Fexp Z.opp bpow]. rewrite !Rmult_1_r. reflexivity.
Qed.

Lemma F2R_0e : forall z, F2R (Float radix2 z 0) = IZR z.
Proof. intros z; unfold F2R; cbn [Fnum Fexp bpow]; ring. Qed.

Section FpToInt.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).
  Hypothesis Hwl : 1 <= wlen <= xlen.
  (* The existing Fpu width condition (`FpCoreRef.v`). *)
  Hypothesis Hxl : xlen + 4 <= 7 * 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation XK := (Bit (e + 3)).
  Local Abbreviation KW := (Bit (xlen + f + 4)).

  Lemma Hxe : xlen + f + 4 <= 2 ^ (e + 2).
  Proof. replace (e + 2) with ((e - 1) + 3) by (pose proof (He e f Hf Hpe); lia). rewrite Z.pow_add_r by (pose proof (He e f Hf Hpe); lia). lia. Qed.

  Lemma Hx1l : 1 <= xlen.
  Proof. lia. Qed.

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  Definition opFI (u w : bool) : type FpOpDK :=
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (true ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (u ,, (w ,, (false ,, tt)))))))))))))))))))))).

  Definition reqFI (u w : bool) (rm : bits 3) (a : bits W) : type (FpReqK e f xlen) :=
    (opFI u w ,, (rm ,, (a ,, (Zmod.zero ,, (Zmod.zero ,, (Zmod.zero ,, tt)))))).

  Definition cvtFIRef (rm : bits 3) (u w : bool) (a : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqFI u w rm a)).

  Lemma cvtFI_core_xres : forall rm u w a,
    (cvtFIRef rm u w a) @% "xres" = (evalLetExpr (fpToInt false e f xlen wlen type rm (negb u) w (unp a))).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma cvtFI_core_flags : forall rm u w a,
    (cvtFIRef rm u w a) @% "flags" = (evalLetExpr (fpToInt false e f xlen wlen type rm (negb u) w (unp a))).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  (* `fpToInt false`, transcribed in two parts: the rounded magnitude, then range check and packing. *)
  Definition fiFront (rm : bits 3) (ua : type (FpUnpK e f)) : bits (xlen + f + 4) * bool * bool :=
    let s := uSign ua in
    let xv := uExp ua in
    let big := evalExpr (Slt (cst (e + 3) (xlen + 1 + expOff false e)) (Var type XK xv)) in
    let sh := evalExpr (Sub (Var type XK xv) (cst (e + 3) (f + expOff false e))) in
    let shNeg := evalExpr (Slt (Var type XK sh) (cst (e + 3) 0)) in
    let amtR0 := evalExpr (Neg (Var type XK sh)) in
    let amtR := evalExpr (ITE (Ult (Var type XK amtR0) (cst (e + 3) (xlen + f + 4))) (Var type XK amtR0) (cst (e + 3) (xlen + f + 4))) in
    let base := evalExpr (Sll (zext (f + 1) (xlen + f + 4) (Var type (Bit (f + 1)) (uSig ua))) (cst (xlen + f + 4) 2)) in
    let nn := evalExpr (ITE (Var type Bool shNeg) (Srl (Var type KW base) (Var type XK amtR))
                            (ITE (Var type Bool big) (cst (xlen + f + 4) 0) (Sll (Var type KW base) (Var type XK sh)))) in
    let stk := evalExpr (And [Var type Bool shNeg; isNotZero (And [Var type KW base; Not (Sll (cst (xlen + f + 4) (-1)) (Var type XK amtR))])]) in
    let lsb := evalExpr (bitSet (ty := type) nn 2) in
    let g := evalExpr (bitSet (ty := type) nn 1) in
    let r := evalExpr (Or [bitSet (ty := type) nn 0; Var type Bool stk]) in
    let inc := evalExpr (roundInc type rm s lsb g r) in
    let inexact := evalExpr (Or [Var type Bool g; Var type Bool r]) in
    let mm := evalExpr (Add [Srl (Var type KW nn) (cst (xlen + f + 4) 2); ITE (Var type Bool inc) (cst (xlen + f + 4) 1) (cst (xlen + f + 4) 0)]) in
    (mm, inexact, big).

  Definition fiBack (sg w : bool) (ua : type (FpUnpK e f)) (big inexact : bool) (mm : bits (xlen + f + 4)) : type (IntOutK xlen) :=
    let s := uSign ua in
    let posLim := evalExpr (ITE (Var type Bool w)
                              (ITE (Var type Bool sg) (cst (xlen + f + 4) (2 ^ (xlen - 1) - 1)) (cst (xlen + f + 4) (2 ^ xlen - 1)))
                              (ITE (Var type Bool sg) (cst (xlen + f + 4) (2 ^ (wlen - 1) - 1)) (cst (xlen + f + 4) (2 ^ wlen - 1)))) in
    let negLim := evalExpr (ITE (Var type Bool sg)
                              (ITE (Var type Bool w) (cst (xlen + f + 4) (2 ^ (xlen - 1))) (cst (xlen + f + 4) (2 ^ (wlen - 1))))
                              (cst (xlen + f + 4) 0)) in
    let inRange := evalExpr (And [Not (Var type Bool big); Not (Var type Bool (uInf ua)); Not (Var type Bool (uNaN ua));
                                  Not (Ult (ITE (Var type Bool s) (Var type KW negLim) (Var type KW posLim)) (Var type KW mm))]) in
    let val := evalExpr (trunc (xlen + f + 4) xlen (ITE (Var type Bool s) (Neg (Var type KW mm)) (Var type KW mm))) in
    let satPos := evalExpr (trunc (xlen + f + 4) xlen (Var type KW posLim)) in
    let satNeg := evalExpr (trunc (xlen + f + 4) xlen (Neg (Var type KW negLim))) in
    let sat := evalExpr (ITE (And [Var type Bool s; Not (Var type Bool (uNaN ua))]) (Var type (Bit xlen) satNeg) (Var type (Bit xlen) satPos)) in
    let raw := evalExpr (ITE (Var type Bool (uZero ua)) (cst xlen 0)
                             (ITE (Var type Bool inRange) (Var type (Bit xlen) val) (Var type (Bit xlen) sat))) in
    let res := evalExpr (ITE (Var type Bool w) (Var type (Bit xlen) raw) (sextW xlen wlen type raw)) in
    let nv := evalExpr (And [Not (Var type Bool (uZero ua)); Not (Var type Bool inRange)]) in
    let nx := evalExpr (And [Not (Var type Bool (uZero ua)); Var type Bool inRange; Var type Bool inexact]) in
    (res ,, (evalExpr (mkFlags type (Var type Bool nv) (ConstBool false) (ConstBool false) (ConstBool false) (Var type Bool nx)) ,, tt)).

  Lemma fpToInt_V : forall rm sg w ua,
    evalLetExpr (fpToInt false e f xlen wlen type rm sg w ua) =
    fiBack sg w ua (snd (fiFront rm ua)) (snd (fst (fiFront rm ua))) (fst (fst (fiFront rm ua))).
  Proof. intros; exact eq_refl. Qed.

  (* The RISC-V integer range of FCVT.{W,WU,L,LU} (`u`: unsigned, `w`: `xlen` bits, else `wlen` bits). *)
  Definition hiZ (u w : bool) : Z :=
    if w then (if u then 2 ^ xlen - 1 else 2 ^ (xlen - 1) - 1) else (if u then 2 ^ wlen - 1 else 2 ^ (wlen - 1) - 1).
  Definition loZ (u w : bool) : Z := if u then 0 else (if w then - 2 ^ (xlen - 1) else - 2 ^ (wlen - 1)).

  (* The integer register value: `wlen`-bit results are sign-extended to XLEN. *)
  Definition encZ (w : bool) (v : Z) : bits xlen := Zmod.of_Z (2 ^ xlen) (if w then v else sextWZ wlen v).

  Lemma back_eval : forall sg w ua big inexact (mm : bits (xlen + f + 4)) Mi,
    Zmod.to_Z mm = Mi -> 0 <= Mi < 2 ^ (xlen + f + 4) ->
    let s := uSign ua in
    let inR := negb big && negb (uInf ua) && negb (uNaN ua) && (Mi <=? (if s then - loZ (negb sg) w else hiZ (negb sg) w)) in
    (fiBack sg w ua big inexact mm).(Fst) =
      encZ w (if uZero ua then 0 else if inR then cond_Zopp s Mi else (if s && negb (uNaN ua) then loZ (negb sg) w else hiZ (negb sg) w)) /\
    (fiBack sg w ua big inexact mm).(Snd).(Fst) =
      mkFl (negb (uZero ua) && negb inR) false false false (negb (uZero ua) && inR && inexact).
  Proof.
    intros sg w ua big inexact mm Mi Hmm HMi s inR.
    destruct ua as [s0 [z0 [i0 [n0 [sn0 [xv [sig []]]]]]]]; cbn [Fst Snd] in *. subst s.
    assert (P32 : 2 ^ wlen <= 2 ^ xlen) by (apply Z.pow_le_mono_r; lia).
    assert (Pw2 : 2 ^ wlen = 2 * 2 ^ (wlen - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Px2 : 2 ^ xlen = 2 * 2 ^ (xlen - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Pw1 : 1 <= 2 ^ (wlen - 1)) by (pose proof (Z.pow_le_mono_r 2 0 (wlen - 1)); lia).
    assert (Px4 : 2 ^ (xlen + 4) <= 2 ^ (xlen + f + 4)) by (apply Z.pow_le_mono_r; lia).
    assert (Pxx : 2 ^ xlen * 16 = 2 ^ (xlen + 4)) by (rewrite Z.pow_add_r by lia; reflexivity).
    assert (HL : 0 <= hiZ (negb sg) w < 2 ^ xlen /\ 0 <= - loZ (negb sg) w <= 2 ^ xlen /\ hiZ (negb sg) w < 2 ^ (xlen + f + 4)).
    { unfold hiZ, loZ; destruct w, sg; cbn [negb]; lia. }
    unfold fiBack; cbv zeta; cbn [Fst Snd].
    match goal with |- context [evalExpr (ITE (Var type Bool w) (ITE (Var type Bool sg) ?a ?b) ?c)] =>
      set (posLim := evalExpr (ITE (Var type Bool w) (ITE (Var type Bool sg) a b) c)) end.
    assert (HpL : Zmod.to_Z posLim = hiZ (negb sg) w).
    { unfold posLim, hiZ in *; destruct w, sg; cbn [evalExpr cst negb] in *; apply tz_ofZ; lia. }
    clearbody posLim.
    match goal with |- context [evalExpr (ITE (Var type Bool sg) (ITE (Var type Bool w) ?a ?b) ?c)] =>
      set (negLim := evalExpr (ITE (Var type Bool sg) (ITE (Var type Bool w) a b) c)) end.
    assert (HnL : Zmod.to_Z negLim = - loZ (negb sg) w).
    { unfold negLim, loZ in *; destruct w, sg; cbn [evalExpr cst negb] in *; rewrite tz_ofZ by lia; lia. }
    clearbody negLim.
    match goal with |- context [evalExpr (And [Not (Var type Bool big); ?a; ?b; ?c])] =>
      set (inRange := evalExpr (And [Not (Var type Bool big); a; b; c])) end.
    assert (HiR : inRange = inR).
    { unfold inRange, inR. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault evalNot andb].
      rewrite Hmm. destruct s0; cbv iota; [rewrite HnL | rewrite HpL]; rewrite Z.leb_antisym; reflexivity. }
    clearbody inRange. subst inRange.
    match goal with |- context [evalExpr (trunc ?i ?o (ITE ?c ?a ?b))] => set (val := evalExpr (trunc i o (ITE c a b))) end.
    assert (Hval : Zmod.to_Z val = (cond_Zopp s0 Mi) mod 2 ^ xlen).
    { unfold val. rewrite unsigned_trunc by lia. cbn [evalExpr]. destruct s0; cbn [cond_Zopp].
      - rewrite neg_eval by lia. cbn [evalExpr]. rewrite Hmm. apply mod_pow2_mod; lia.
      - rewrite Hmm. reflexivity. }
    clearbody val.
    match goal with |- context [evalExpr (trunc ?i ?o (Var type (Bit (xlen + f + 4)) posLim))] => set (satPos := evalExpr (trunc i o (Var type (Bit (xlen + f + 4)) posLim))) end.
    assert (HsP : Zmod.to_Z satPos = hiZ (negb sg) w mod 2 ^ xlen).
    { unfold satPos. rewrite unsigned_trunc by lia. cbn [evalExpr]. rewrite HpL. reflexivity. }
    clearbody satPos.
    match goal with |- context [evalExpr (trunc ?i ?o (Neg ?a))] => set (satNeg := evalExpr (trunc i o (Neg a))) end.
    assert (HsN : Zmod.to_Z satNeg = loZ (negb sg) w mod 2 ^ xlen).
    { unfold satNeg. rewrite unsigned_trunc by lia. rewrite neg_eval by lia. cbn [evalExpr]. rewrite HnL, Z.opp_involutive.
      apply mod_pow2_mod; lia. }
    clearbody satNeg.
    set (V := if z0 then 0 else if inR then cond_Zopp s0 Mi else (if s0 && negb n0 then loZ (negb sg) w else hiZ (negb sg) w)).
    match goal with |- context [evalExpr (ITE (Var type Bool z0) ?a ?b)] => set (raw := evalExpr (ITE (Var type Bool z0) a b)) end.
    assert (Hraw : Zmod.to_Z raw = V mod 2 ^ xlen).
    { unfold raw, V. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault evalNot andb cst].
      destruct z0; [rewrite Zmod.unsigned_of_Z; reflexivity |].
      destruct inR; [exact Hval |]. destruct (s0 && negb n0); assumption. }
    clearbody raw.
    split.
    - cbn [Fst]. unfold encZ. fold V. destruct w; cbn [evalExpr].
      + apply Zmod.unsigned_inj. rewrite Hraw, Zmod.unsigned_of_Z. reflexivity.
      + rewrite sextW_eval by lia. rewrite Hraw, sextWZ_mod by lia. reflexivity.
    - cbn [Snd Fst]. rewrite mkFlags_evalV. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault evalNot andb].
      reflexivity.
  Qed.

  Lemma HeI : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  (* A finite non-zero operand with unbiased exponent at most `xlen + 1`: the rounded magnitude. *)
  Lemma front_fin : forall rm a s E M,
    0 <= M < 2 ^ f -> 0 <= E < 2 ^ e -> Zmod.to_Z a = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    E <> 2 ^ e - 1 -> (E <> 0 \/ M <> 0) -> Zmod.signed (uExp (unp a)) <= xlen + 1 ->
    snd (fiFront rm (unp a)) = false /\
    exists Mi, 0 <= Mi < 2 ^ (xlen + 4) /\ Zmod.to_Z (fst (fst (fiFront rm (unp a)))) = Mi /\
      round_mode (modeOf rm) (BinarySingleNaN.B2R (toB a)) = cond_Zopp s Mi /\
      snd (fst (fiFront rm (unp a))) = negb (Req_bool (IZR (cond_Zopp s Mi)) (BinarySingleNaN.B2R (toB a))).
  Proof.
    intros rm a s E M HM HE Ha Hn Hz HXb.
    pose proof HeI as He2.
    pose proof (fin_facts e f Hf Hpe a s E M HM HE Ha Hn Hz) as FF; cbv beta zeta in FF.
    destruct FF as (HSg & HX & HV & _ & _).
    pose proof (u_sign e f He2 Hf a s E M HM HE Ha) as Hus.
    set (v := BinarySingleNaN.B2R (toB a)) in *. clearbody v.
    set (ua := unp a) in *. clearbody ua.
    destruct ua as [s0 [z0 [i0 [n0 [sn0 [xv [sig []]]]]]]]; cbn [Fst Snd] in *. subst s0.
    set (X := Zmod.signed xv) in *. set (Sg := Zmod.to_Z sig) in *.
    assert (HXd : Zmod.signed xv = X) by reflexivity. assert (HSd : Zmod.to_Z sig = Sg) by reflexivity.
    clearbody X Sg. clear Ha HM HE Hn Hz.
    unfold fpEmin, fpEmax, fpBias in HX.
    assert (P2 : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (P3 : 2 ^ (e + 3) = 16 * 2 ^ (e - 1)) by (replace (e + 3) with ((e - 1) + 4) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Pf1 : 2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (Pf3 : 2 ^ (f + 3) = 8 * 2 ^ f) by (rewrite Z.pow_add_r by lia; change (2 ^ 3) with 8; lia).
    assert (Pf3x : 2 ^ (f + 3) <= 2 ^ (xlen + f + 4)) by (apply Z.pow_le_mono_r; lia).
    unfold fiFront; cbv zeta; cbn [fst snd Fst Snd].
    (* big = false *)
    rewrite (slt_eval (e + 3)) by lia.
    change (evalExpr (Var type (Bit (e + 3)) xv)) with xv.
    change (evalExpr (cst (e + 3) (xlen + 1 + expOff false e))) with (Zmod.of_Z (2 ^ (e + 3)) (xlen + 1 + 0)).
    rewrite signed_k, HXd by lia.
    replace (xlen + 1 + 0 <? X) with false by (symmetry; apply Z.ltb_ge; lia).
    split; [reflexivity |].
    match goal with |- context [evalExpr (Sub ?c ?d)] => set (sh := evalExpr (Sub c d)) end.
    assert (Hsh : sh = Zmod.of_Z (2 ^ (e + 3)) (X - f)).
    { unfold sh. rewrite (sub_eval (e + 3)) by lia. cbn [evalExpr cst expOff].
      rewrite <- (Zmod.of_Z_signed xv), HXd, <- Zmod.of_Z_sub. f_equal; lia. }
    clearbody sh. subst sh.
    assert (Hshs : Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) (X - f)) = X - f) by (apply signed_k; lia).
    rewrite (slt_eval (e + 3)) by lia.
    change (evalExpr (Var type (Bit (e + 3)) (Zmod.of_Z (2 ^ (e + 3)) (X - f)))) with (Zmod.of_Z (2 ^ (e + 3)) (X - f)).
    change (evalExpr (@cst type (e + 3) 0)) with (Zmod.of_Z (2 ^ (e + 3)) 0).
    rewrite Hshs, (signed_k e He2 0) by lia.
    match goal with |- context [evalExpr (Sll (zext ?i ?o ?x) ?c)] => set (base := evalExpr (Sll (zext i o x) c)) end.
    assert (Hbase : Zmod.to_Z base = Sg * 4).
    { unfold base. cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr cst].
      assert (4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
      rewrite (tz_ofZ (xlen + f + 4) 2) by lia.
      rewrite HSd, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. apply Z.mod_small; lia. }
    clearbody base.
    match goal with |- context [evalExpr (Neg ?a)] => set (amtR0 := evalExpr (Neg a)) end.
    assert (HamtR0 : X < f -> Zmod.to_Z amtR0 = f - X).
    { intros Hlt. unfold amtR0. rewrite neg_eval by lia. cbn [evalExpr]. rewrite Zmod.unsigned_of_Z.
      rewrite <- (Z.mod_unique (X - f) (2 ^ (e + 3)) (-1) (X - f + 2 ^ (e + 3))) by lia.
      symmetry; apply Z.mod_unique with (-1); lia. }
    clearbody amtR0.
    match goal with |- context [evalExpr (ITE (Ult ?a ?b) ?c ?d)] => set (amtR := evalExpr (ITE (Ult a b) c d)) end.
    set (D := Z.min (f - X) (xlen + f + 4)).
    assert (Hamt : X < f -> Zmod.to_Z amtR = D).
    { intros Hlt. unfold amtR, D. cbn [evalExpr cst]. rewrite (HamtR0 Hlt), (tz_ofZ (e + 3) (xlen + f + 4)) by lia.
      destruct (Z.ltb_spec (f - X) (xlen + f + 4)); [rewrite (HamtR0 Hlt); lia | rewrite tz_ofZ by lia; lia]. }
    clearbody amtR.
    match goal with |- context [evalExpr (ITE (Var type Bool (X - f <? 0)) ?a ?b)] =>
      set (nn := evalExpr (ITE (Var type Bool (X - f <? 0)) a b)) end.
    set (NN := if X <? f then Sg * 4 / 2 ^ D else Sg * 4 * 2 ^ (X - f)).
    assert (Hnn : Zmod.to_Z nn = NN).
    { unfold nn, NN. cbn [evalExpr cst]. destruct (Z.ltb_spec (X - f) 0); destruct (Z.ltb_spec X f); try lia; cbv iota.
      - rewrite tz_sru by lia. rewrite Hbase, Hamt by lia. reflexivity.
      - rewrite bits.unsigned_slu, Zmod.unsigned_of_Z, (Z.mod_small (X - f)), Hbase, Z.shiftl_mul_pow2 by lia.
        apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; lia |].
        assert (2 ^ (f + 3) * 2 ^ (X - f) <= 2 ^ (xlen + f + 4)) by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia).
        assert (0 < 2 ^ (X - f)) by (apply Z.pow_pos_nonneg; lia).
        apply Z.lt_le_trans with (2 ^ (f + 3) * 2 ^ (X - f)); [apply Z.mul_lt_mono_pos_r; lia | lia]. }
    clearbody nn.
    match goal with |- context [evalExpr (And [Var type Bool (X - f <? 0); ?t])] =>
      set (stk := evalExpr (And [Var type Bool (X - f <? 0); t])) end.
    set (ST := (X <? f) && negb ((Sg * 4) mod 2 ^ D =? 0)).
    assert (Hstk : stk = ST).
    { unfold stk, ST. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault andb].
      replace (X - f <? 0) with (X <? f) by (destruct (Z.ltb_spec (X - f) 0), (Z.ltb_spec X f); lia || reflexivity).
      destruct (Z.ltb_spec X f) as [Hlt | Hge]; [| reflexivity]. cbn [andb].
      rewrite evalExpr_isNotZero_bits. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd evalNot cst].
      rewrite unsigned_and_m1_l by lia. rewrite tz_lowmask by (rewrite (Hamt Hlt); lia). rewrite Hbase, (Hamt Hlt). reflexivity. }
    clearbody stk. subst stk.
    rewrite !bitSet_testbit by lia. rewrite roundInc_eval, Hnn.
    assert (HNN : 0 <= NN) by (unfold NN; destruct (Z.ltb_spec X f); [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; unfold D; lia] |
                                                              apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]]).
    assert (HNNd : NN = if X <? f then Sg * 4 / 2 ^ D else Sg * 4 * 2 ^ (X - f)) by reflexivity. clearbody NN.
    remember (rmInc (Zmod.to_Z rm) s (Z.testbit NN 2) (Z.testbit NN 1) (Z.testbit NN 0 || ST)) as inc eqn:Hincd.
    (* the location of |v| *)
    assert (Hpos : (0 < F2R (Float radix2 Sg (X - f)))%R) by (apply F2R_gt_0; cbn; lia).
    assert (Hs : Rlt_bool v 0 = s) by (rewrite HV; apply Rlt_bool_cond_Ropp; exact Hpos).
    assert (Hav : Rabs v = F2R (Float radix2 (Sg * 4) (X - f - 2))).
    { rewrite HV, abs_cond_Ropp, Rabs_pos_eq by lra. change 4 with (2 ^ 2). rewrite F2R_scale by lia. reflexivity. }
    assert (Hloc : inbetween_float radix2 (NN / 4) 0 (Rabs v) (locOf (Z.testbit NN 1) (Z.testbit NN 0 || ST))).
    { destruct (Z.ltb_spec X f) as [Hlt | Hge].
      - assert (Hin0 : inbetween_float radix2 (Sg * 4) (X - f - 2) (Rabs v) loc_Exact) by (constructor; exact Hav).
        destruct (loc_shift (Rabs v) (Sg * 4) (X - f - 2) loc_Exact false (f - X) ltac:(lia) Hin0 ltac:(split; reflexivity))
          as (l1 & Hl1 & Hl1e).
        assert (Eq : Sg * 4 / 2 ^ (f - X) = NN /\ (Sg * 4) mod 2 ^ (f - X) = (Sg * 4) mod 2 ^ D).
        { rewrite HNNd; try rewrite (proj2 (Z.ltb_lt _ _) Hlt). unfold D.
          destruct (Z.le_ge_cases (f - X) (xlen + f + 4)) as [Hd | Hd]; [rewrite Z.min_l by lia; split; reflexivity |].
          rewrite Z.min_r by lia.
          assert (2 ^ (xlen + f + 4) <= 2 ^ (f - X)) by (apply Z.pow_le_mono_r; lia).
          rewrite !Z.div_small, !Z.mod_small by lia; split; reflexivity. }
        destruct Eq as [E1 E2]; rewrite E1 in Hl1; rewrite E2 in Hl1e. cbn [orb] in Hl1e.
        unfold ST; try rewrite (proj2 (Z.ltb_lt _ _) Hlt); cbn [andb].
        pose proof (loc_drop2 _ _ _ _ _ Hl1 Hl1e) as Hl. replace (X - f - 2 + (f - X) + 2) with 0 in Hl by lia. exact Hl.
      - unfold ST; try rewrite (proj2 (Z.ltb_ge _ _) Hge); cbn [andb]. rewrite HNNd; try rewrite (proj2 (Z.ltb_ge _ _) Hge).
        replace (Sg * 4 * 2 ^ (X - f)) with ((Sg * 2 ^ (X - f)) * 2 ^ 2) by (change (2 ^ 2) with 4; ring).
        rewrite Z.div_mul by (change (2 ^ 2) with 4; lia).
        rewrite !Z.mul_pow2_bits_low by lia. cbn [locOf orb]. constructor.
        rewrite HV, abs_cond_Ropp, Rabs_pos_eq by lra. replace (X - f) with (0 + (X - f)) at 1 by lia.
        replace 0%Z with ((X - f) - (X - f)) at 2 by lia. rewrite F2R_scale by lia. f_equal; f_equal; lia. }
    assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)); change (2 ^ 3) with 8 in *; lia).
    pose proof (round_at (FIX_exp 0) (Zmod.to_Z rm) s v (NN / 4) 0 _ _ Hrm Hs eq_refl Hloc) as Hr.
    rewrite <- testbit2_odd, <- Hincd in Hr by lia.
    set (Mi := NN / 4 + b2z inc) in *.
    assert (HMid : Mi = NN / 4 + b2z inc) by reflexivity. clearbody Mi.
    assert (HMi : 0 <= Mi <= 2 ^ (xlen + 2)).
    { assert (H4 : NN / 4 < 2 ^ (xlen + 2)).
      { rewrite HNNd. destruct (Z.ltb_spec X f) as [Hlt | Hge].
        - assert (0 < 2 ^ D) by (apply Z.pow_pos_nonneg; unfold D; lia).
          rewrite Z.div_div by lia. apply Z.div_lt_upper_bound; [lia |].
          replace (2 ^ D * 4 * 2 ^ (xlen + 2)) with (2 ^ (xlen + 4 + D))
            by (rewrite !Z.pow_add_r by (unfold D; lia); change (2 ^ 4) with 16; change (2 ^ 2) with 4; ring).
          assert (2 ^ (f + 3) <= 2 ^ (xlen + 4 + D)) by (apply Z.pow_le_mono_r; unfold D; lia). lia.
        - replace (Sg * 4 * 2 ^ (X - f)) with ((Sg * 2 ^ (X - f)) * 4) by ring. rewrite Z.div_mul by lia.
          assert (2 ^ (f + 1) * 2 ^ (X - f) <= 2 ^ (xlen + 2)) by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia).
          assert (0 < 2 ^ (X - f)) by (apply Z.pow_pos_nonneg; lia).
          apply Z.lt_le_trans with (2 ^ (f + 1) * 2 ^ (X - f)); [apply Z.mul_lt_mono_pos_r; lia | lia]. }
      assert (0 <= NN / 4) by (apply Z.div_pos; lia). rewrite HMid; destruct inc; cbn [b2z]; lia. }
    exists Mi. split; [split; [lia | ] |].
    { assert (2 ^ (xlen + 2) < 2 ^ (xlen + 4)) by (apply Z.pow_lt_mono_r; lia). lia. }
    split; [| split].
    - (* the integer magnitude *)
      assert (Hx4 : 2 ^ (xlen + 2) < 2 ^ (xlen + f + 4)) by (apply Z.pow_lt_mono_r; lia).
      cbn [evalExpr fold_left map cst evalOrBinary evalBinary KindCustomInd getDefault orb].
      rewrite !Zmod.unsigned_add, Zmod.unsigned_0. rewrite !bitSet_testbit by lia.
      assert (4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
      rewrite (tz_ofZ (xlen + f + 4) 2), tz_sru by lia. rewrite !Hnn. change (2 ^ 2) with 4.
      assert (0 <= NN / 4) by (apply Z.div_pos; lia).
      assert (NN / 4 < 2 ^ (xlen + f + 4)) by (rewrite HMid in HMi; destruct inc; cbn [b2z] in HMi; lia).
      rewrite HMid in HMi |- *. try rewrite <- Hincd. clear Hincd. destruct inc; cbn [b2z] in *; cbv iota; rewrite tz_ofZ by lia;
        rewrite Z.add_0_l, (Z.mod_small (NN / 4)) by lia; apply Z.mod_small; lia.
    - change (modeOf rm) with (modeZ (Zmod.to_Z rm)). apply eq_IZR. rewrite <- round_FIX0 by apply valid_rnd_round_mode.
      rewrite Hr, F2R_0e. reflexivity.
    - (* inexact *)
      cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault orb].
      rewrite !bitSet_testbit by lia. rewrite Hnn, <- F2R_0e, HMid.
      rewrite (exact_iff s v (NN / 4) 0 _ (b2z inc) Hs Hloc ltac:(apply Z.div_pos; lia)).
      + destruct (Z.testbit NN 1), (Z.testbit NN 0 || ST); reflexivity.
      + rewrite Hincd; destruct (Z.testbit NN 1), (Z.testbit NN 0 || ST); cbn [locOf];
          intros H; try discriminate H; rewrite rmInc_exact; reflexivity.
      + destruct inc; cbn [b2z]; lia.
  Qed.

  Lemma front_big : forall rm (ua : type (FpUnpK e f)), xlen + 1 < Zmod.signed (uExp ua) -> snd (fiFront rm ua) = true.
  Proof.
    intros rm ua H. pose proof HeI as He2.
    assert (P2 : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    unfold fiFront; cbv zeta; cbn [fst snd]. rewrite (slt_eval (e + 3)) by lia.
    change (evalExpr (cst (e + 3) (xlen + 1 + expOff false e))) with (Zmod.of_Z (2 ^ (e + 3)) (xlen + 1 + 0)).
    rewrite signed_k by lia. apply Z.ltb_lt. cbv beta in *. cbn [evalExpr]. lia.
  Qed.

  (* The spec: FCVT.{W,WU,L,LU}.fmt with Flocq's rounding of the operand to an integer. *)
  Definition fiSpec (rm : bits 3) (u w : bool) (a : bits W) : bits xlen * bits 5 :=
    match toB a with
    | BinarySingleNaN.B754_nan => (encZ w (hiZ u w), mkFl true false false false false)
    | BinarySingleNaN.B754_infinity s => (encZ w (if s then loZ u w else hiZ u w), mkFl true false false false false)
    | BinarySingleNaN.B754_zero _ => (encZ w 0, mkFl false false false false false)
    | BinarySingleNaN.B754_finite s _ _ _ =>
        let n := round_mode (modeOf rm) (BinarySingleNaN.B2R (toB a)) in
        if (loZ u w <=? n) && (n <=? hiZ u w)
        then (encZ w n, mkFl false false false false (negb (Req_bool (IZR n) (BinarySingleNaN.B2R (toB a)))))
        else (encZ w (if s then loZ u w else hiZ u w), mkFl true false false false false)
    end.

  Definition cvtFI_flocq : Prop :=
    forall rm u w a,
      (cvtFIRef rm u w a) @% "xres" = fst (fiSpec rm u w a) /\ (cvtFIRef rm u w a) @% "flags" = snd (fiSpec rm u w a).

  Lemma range_iff : forall u w s Mi, 0 <= Mi ->
    (loZ u w <=? cond_Zopp s Mi) && (cond_Zopp s Mi <=? hiZ u w) = (Mi <=? (if s then - loZ u w else hiZ u w)).
  Proof.
    intros u w s Mi HM. assert (Hl : loZ u w <= 0) by (unfold loZ; destruct u, w; lia).
    assert (Hh : 0 <= hiZ u w) by (unfold hiZ; destruct u, w; lia).
    destruct s; cbn [cond_Zopp].
    - destruct (Z.leb_spec (loZ u w) (- Mi)), (Z.leb_spec (- Mi) (hiZ u w)), (Z.leb_spec Mi (- loZ u w)); try lia; reflexivity.
    - destruct (Z.leb_spec (loZ u w) Mi), (Z.leb_spec Mi (hiZ u w)); try lia; reflexivity.
  Qed.

  Theorem cvtFI_flocq_holds : cvtFI_flocq.
  Proof.
    intros rm u w a. rewrite cvtFI_core_xres, cvtFI_core_flags, fpToInt_V.
    pose proof HeI as He2.
    destruct (split_fields e f Hf Hpe a) as (s & E & M & HM & HE & Ha).
    pose proof (cls e f Hf Hpe a s E M HM HE Ha) as C.
    pose proof (u_nan e f He2 Hf a s E M HM HE Ha) as Hun. pose proof (u_inf e f He2 Hf a s E M HM HE Ha) as Hui.
    pose proof (u_zero e f He2 Hf a s E M HM HE Ha) as Huz. pose proof (u_sign e f He2 Hf a s E M HM HE Ha) as Hus.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    set (fr := fiFront rm (unp a)).
    pose proof (bits.unsigned_range (fst (fst fr)) ltac:(lia)) as Hmmr.
    destruct (back_eval (negb u) w (unp a) (snd fr) (snd (fst fr)) (fst (fst fr)) _ eq_refl Hmmr) as (B1 & B2).
    rewrite B1, B2; clear B1 B2. rewrite negb_involutive. cbv beta. rewrite Hun, Hui, Huz, Hus.
    unfold fiSpec.
    destruct (Z.eq_dec E (2 ^ e - 1)) as [HE1 | HE1]; [destruct (Z.eq_dec M 0) as [HM0 | HM0] |].
    - (* infinity *)
      rewrite HE1, HM0, !Z.eqb_refl. cbn [andb negb].
      destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
      destruct C as (-> & _). rewrite ?Z.eqb_refl, ?andb_false_r.
      replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. destruct s; split; reflexivity.
    - (* NaN *)
      rewrite HE1, !Z.eqb_refl. replace (M =? 0) with false by (symmetry; apply Z.eqb_neq; exact HM0). cbn [andb negb].
      destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
      rewrite ?andb_false_r. try replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb negb]. destruct s; split; reflexivity.
    - replace ((E =? 2 ^ e - 1) && negb (M =? 0)) with false by (destruct (Z.eqb_spec E (2 ^ e - 1)); [lia | reflexivity]).
      replace ((E =? 2 ^ e - 1) && (M =? 0)) with false by (destruct (Z.eqb_spec E (2 ^ e - 1)); [lia | reflexivity]).
      assert (Hzd : (E = 0 /\ M = 0) \/ (E <> 0 \/ M <> 0)) by lia.
      destruct Hzd as [[HE0 HM0] | Hz].
      + (* zero *)
        rewrite HE0, HM0. change ((0 =? 0) && (0 =? 0)) with true. cbn [andb negb].
        destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
        split; reflexivity.
      + replace ((E =? 0) && (M =? 0)) with false by (destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); try reflexivity; lia).
        cbn [andb negb].
        destruct (Z_le_gt_dec (Zmod.signed (uExp (unp a))) (xlen + 1)) as [Hs | Hb].
        * destruct (front_fin rm a s E M HM HE Ha HE1 Hz ltac:(cbv beta; lia)) as (F1 & Mi & HMi & F2 & F3 & F4).
          fold fr in F1, F2, F4. rewrite F1, F2, F4. cbn [andb negb].
          destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hbb; cbn [clsP] in C; try lia.
          destruct C as (-> & _). cbv zeta. rewrite F3, range_iff by lia.
          destruct (Mi <=? (if s then - loZ u w else hiZ u w)); rewrite ?andb_true_r; split; reflexivity.
        * pose proof (front_big rm (unp a) (Z.gt_lt _ _ Hb)) as F1. fold fr in F1. rewrite F1. cbn [andb negb].
          pose proof (fin_facts e f Hf Hpe a s E M HM HE Ha HE1 Hz) as FF; cbv beta zeta in FF.
          destruct FF as (HSg & _ & HV & _ & _). cbv beta in Hb.
          match type of HV with context [F2R (Float radix2 ?x (?y - f))] => set (Sg0 := x) in *; set (X0 := y) in * end.
          clearbody Sg0 X0.
          assert (HK : (IZR (2 ^ (xlen + 2)) <= F2R (Float radix2 Sg0 (X0 - f)))%R).
          { rewrite <- bpow_2 by lia. apply Rle_trans with (bpow radix2 ((X0 - f) + f)); [apply bpow_le; lia |].
            apply ge_scaled; cbn [Fnum]; lia. }
          assert (Pwx : 2 ^ wlen <= 2 ^ xlen) by (apply Z.pow_le_mono_r; lia).
          assert (Px2 : 2 ^ (xlen + 2) = 4 * 2 ^ xlen) by (rewrite Z.pow_add_r by lia; lia).
          assert (Pw2 : 2 ^ wlen = 2 * 2 ^ (wlen - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
          assert (Pxx : 2 ^ xlen = 2 * 2 ^ (xlen - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
          assert (Hhl : hiZ u w < 2 ^ (xlen + 2) /\ - 2 ^ (xlen + 2) < loZ u w).
          { unfold hiZ, loZ. destruct w, u; lia. }
          destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hbb; cbn [clsP] in C; try lia.
          destruct C as (-> & _). cbv zeta.
          set (n := round_mode (modeOf rm) (BinarySingleNaN.B2R (BinarySingleNaN.B754_finite s m' ex' Hb'))).
          assert (Hn : (s = false -> 2 ^ (xlen + 2) <= n) /\ (s = true -> n <= - 2 ^ (xlen + 2))).
          { split; intros Hs0.
            - unfold n. rewrite <- (Zrnd_IZR (round_mode (modeOf rm)) (2 ^ (xlen + 2))).
              apply (Zrnd_le (round_mode (modeOf rm))). rewrite HV, Hs0. exact HK.
            - unfold n. rewrite <- (Zrnd_IZR (round_mode (modeOf rm)) (- 2 ^ (xlen + 2))).
              apply (Zrnd_le (round_mode (modeOf rm))). rewrite HV, Hs0, opp_IZR. cbn [cond_Ropp]. lra. }
          replace ((loZ u w <=? n) && (n <=? hiZ u w)) with false
            by (destruct s; [destruct Hn as [_ Hn]; specialize (Hn eq_refl) | destruct Hn as [Hn _]; specialize (Hn eq_refl)];
                destruct (Z.leb_spec (loZ u w) n), (Z.leb_spec n (hiZ u w)); try lia; reflexivity).
          rewrite ?andb_true_r. split; reflexivity.
  Qed.
End FpToInt.
