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
 * FSQRT against Flocq's `Bsqrt` (`Sqrt.v`).
 *
 * `fsqrtRef rm a` is the reference core (`FpCoreRef.fpuComputeRef`) on a decoded FSQRT.
 * `fsqrt_flocq`: its result is Flocq's `Bsqrt` (in `BinarySingleNaN`, NaN encoded as the RISC-V
 * canonical NaN) and its flags are the IEEE flags of rounding the exact square root (`Flags.v`),
 * with NV for a signaling NaN or a negative non-zero operand.
 *
 * The restoring square-root loop (`sqrtIter`) is proved by a loop invariant: after consuming the
 * top `2 i` bits `P` of the radicand, `root = floor(sqrt P)` and `rem = P - root^2`.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket Calc.Sqrt IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ---------------------------------------------------------------------------
 * Integer facts
 * --------------------------------------------------------------------------- *)

(* `a * 2^k` and a `k`-bit `t` have disjoint bits. *)
Lemma lor_mulpow : forall a k t, 0 <= a -> 0 <= k -> 0 <= t < 2 ^ k -> Z.lor (a * 2 ^ k) t = a * 2 ^ k + t.
Proof.
  intros a k t Ha Hk Ht.
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor; [reflexivity | |];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
    rewrite Z.mul_pow2_bits by lia;
    (destruct (Z.lt_ge_cases i k) as [Hi2 | Hi2];
     [rewrite (Z.testbit_neg_r a (i - k)) by lia; reflexivity |
      destruct (Z.eq_dec t 0) as [-> | Ht0]; [rewrite Z.bits_0; apply andb_false_r |];
      rewrite (Z.bits_above_log2 t i); [apply andb_false_r | lia |];
      assert (Z.log2 t < k) by (apply Z.log2_lt_pow2; lia); lia]).
Qed.

Lemma lor_mul4 : forall a t, 0 <= a -> 0 <= t < 4 -> Z.lor (a * 4) t = a * 4 + t.
Proof. intros a t Ha Ht; change 4 with (2 ^ 2) in *; apply lor_mulpow; lia. Qed.

Lemma lor_mul2 : forall a t, 0 <= a -> 0 <= t < 2 -> Z.lor (a * 2) t = a * 2 + t.
Proof. intros a t Ha Ht; rewrite <- (Z.pow_1_r 2) in *; apply lor_mulpow; lia. Qed.

(* One step of the restoring square root, on integers. *)
Lemma isqrt_step : forall P q m t, q * q + m = P -> 0 <= m <= 2 * q -> 0 <= t < 4 ->
  let rS := 4 * m + t in let ge := 4 * q + 1 <=? rS in
  let q' := 2 * q + b2z ge in let m' := if ge then rS - (4 * q + 1) else rS in
  q' * q' + m' = 4 * P + t /\ 0 <= m' <= 2 * q'.
Proof.
  intros P q m t HP Hm Ht rS ge q' m'.
  unfold q', m', ge, rS; destruct (Z.leb_spec (4 * q + 1) (4 * m + t)); cbn [b2z]; split; nia.
Qed.

Section Sqrt.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).

  (* Flocq's side conditions, as the instances its operations expect. *)
  Local Instance precGt : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  (* The decoded FSQRT (`FpCore.FpOpDK`): only the `sqrt` family flag is set. *)
  Definition opSqrt : type FpOpDK :=
    (false ,, (false ,, (false ,, (false ,, (true ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (false ,, (false ,, (false ,, tt)))))))))))))))))))))).

  (* FSQRT in the reference core. *)
  Definition fsqrtRef (rm : bits 3) (a : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqOf e f xlen opSqrt rm a Zmod.zero Zmod.zero Zmod.zero)).

  (* IEEE flags of FSQRT. *)
  Definition sqrtFlags (rm : bits 3) (a : bits W) : bits 5 :=
    match toB a with
    | BinarySingleNaN.B754_nan => mkFl (isSNaN e f Hf Hpe a) false false false false
    | BinarySingleNaN.B754_infinity true | BinarySingleNaN.B754_finite true _ _ _ => mkFl true false false false false
    | BinarySingleNaN.B754_finite false _ _ _ =>
        finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) (sqrt (BinarySingleNaN.B2R (toB a)))
    | _ => mkFl false false false false false
    end.

  Definition fsqrt_flocq : Prop :=
    forall rm a,
      (fsqrtRef rm a) @% "res" = ofB (BinarySingleNaN.Bsqrt (modeOf rm) (toB a)) /\
      (fsqrtRef rm a) @% "flags" = sqrtFlags rm a.

  (* ---------------------------------------------------------------------------
   * The FSQRT path of the core
   * --------------------------------------------------------------------------- *)

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  Definition initS (rm : bits 3) (a : bits W) : type (SqrtStateK e f) :=
    evalLetExpr (sqrtInit false e f xlen type (reqOf e f xlen opSqrt rm a Zmod.zero Zmod.zero Zmod.zero)).

  Definition sqrtCore (rm : bits 3) (a : bits W) : type (FpOutK e f) :=
    evalLetExpr (sqrtFinish false e f type (evalLetExpr (sqrtIter e f type (sqrtSteps f) (initS rm a)))).

  Lemma fsqrt_core_res : forall rm a, (fsqrtRef rm a) @% "res" = (sqrtCore rm a).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma fsqrt_core_flags : forall rm a, (fsqrtRef rm a) @% "flags" = (sqrtCore rm a).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  (* `sqrtInit false`, transcribed. *)
  Definition oddV (ua : type (FpUnpK e f)) : bool :=
    evalExpr (bitSet (ty := type) (evalExpr (Add [Var type (Bit (e + 3)) (uExp ua); cst (e + 3) (expOff false e)])) 0).

  Lemma initS_info : forall rm a, (initS rm a).(Fst) = (rm ,, (a ,, (unp a ,, tt))).
  Proof. intros; exact eq_refl. Qed.

  Lemma initS_rad : forall rm a, (initS rm a).(Snd).(Fst) =
    evalExpr (Sll (zext (f + 1) (2 * f + 6) (Var type (Bit (f + 1)) (uSig (unp a))))
                  (ITE (Var type Bool (oddV (unp a))) (cst (2 * f + 6) (f + 5)) (cst (2 * f + 6) (f + 4)))).
  Proof. intros; exact eq_refl. Qed.

  Lemma initS_rem : forall rm a, (initS rm a).(Snd).(Snd).(Fst) = Zmod.of_Z _ 0.
  Proof. intros; exact eq_refl. Qed.

  Lemma initS_root : forall rm a, (initS rm a).(Snd).(Snd).(Snd).(Fst) = Zmod.of_Z _ 0.
  Proof. intros; exact eq_refl. Qed.

  (* `sqrtFinish false`, transcribed. *)
  Definition finV (sn : type (SqrtStateK e f)) : type (FpOutK e f) :=
    let rm := sn.(Fst).(Fst) in
    let a := sn.(Fst).(Snd).(Fst) in
    let ua := sn.(Fst).(Snd).(Snd).(Fst) in
    let sti := evalExpr (isNotZero (Var type (Bit (f + 5)) sn.(Snd).(Snd).(Fst))) in
    let xr := evalExpr (Sra (Add [Var type (Bit (e + 3)) (uExp ua); cst (e + 3) (expOff false e)]) (cst 1 1)) in
    if uNaN ua
    then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool (uSNaN ua)) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if uZero ua then (a ,, (Zmod.of_Z _ 0 ,, tt))
    else if uSign ua
    then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if uInf ua then (a ,, (Zmod.of_Z _ 0 ,, tt))
    else evalLetExpr (normRound false e f type (f + 3) false xr sn.(Snd).(Snd).(Snd).(Fst) sti rm).

  Lemma sqrtFinish_V : forall sn, evalLetExpr (sqrtFinish false e f type sn) = finV sn.
  Proof. intros; exact eq_refl. Qed.

  Lemma He0 : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Lemma add0_val : forall u : bits (e + 3),
    evalExpr (Add [Var type (Bit (e + 3)) u; cst (e + 3) (expOff false e)]) = u.
  Proof. intros u; cbn [evalExpr fold_left map cst]; unfold expOff; rewrite Zmod.of_Z_0, Zmod.add_0_l, Zmod.add_0_r; reflexivity. Qed.

  Lemma oddV_val : forall ua, oddV ua = Z.odd (Zmod.signed (uExp ua)).
  Proof.
    intros ua; pose proof He0. unfold oddV; rewrite add0_val, bitSet_testbit, Z.bit0_odd by lia.
    set (u := uExp ua). rewrite <- (Zmod.of_Z_signed u) at 1. rewrite Zmod.unsigned_of_Z.
    set (z := Zmod.signed u). set (M := 2 ^ (e + 2)).
    assert (E : 2 ^ (e + 3) = 2 * M) by (unfold M; rewrite (Z.pow_add_r 2 e 3), (Z.pow_add_r 2 e 2) by lia; lia).
    assert (0 < M) by (apply Z.pow_pos_nonneg; lia).
    rewrite E. rewrite (Z.div_mod z (2 * M)) at 2 by lia. rewrite <- Z.mul_assoc, Z.add_comm, Z.odd_add_mul_2. reflexivity.
  Qed.

  Lemma xr_val : forall u : bits (e + 3),
    Zmod.signed (evalExpr (Sra (Add [Var type (Bit (e + 3)) u; cst (e + 3) (expOff false e)]) (cst 1 1))) = Zmod.signed u / 2.
  Proof.
    intros u; pose proof He0.
    change (Zmod.signed (Zmod.srs (evalExpr (Add [Var type (Bit (e + 3)) u; cst (e + 3) (expOff false e)]))
                                  (Zmod.to_Z (evalExpr (@cst type 1 1)))) = Zmod.signed u / 2).
    rewrite add0_val. cbn [evalExpr cst]. rewrite Zmod.unsigned_of_Z. change (1 mod 2 ^ 1) with 1.
    rewrite Zmod.signed_srs by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma normRound_f3 : forall s x (wsig : bits (f + 3)) st rm, 2 ^ (f + 2) <= Zmod.to_Z wsig ->
    evalLetExpr (normRound false e f type (f + 3) s x wsig st rm) = evalLetExpr (roundPack false e f type s x wsig st rm).
  Proof.
    intros s x wsig st rm Hw. pose proof He0.
    pose proof (bits.unsigned_range wsig ltac:(lia)) as Hr.
    assert (HP : 2 ^ (f + 3) = 2 * 2 ^ (f + 2)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (HL : Z.log2 (Zmod.to_Z wsig) = f + 2) by (apply Z.log2_unique; [lia |]; replace (Z.succ (f + 2)) with (f + 3) by lia; lia).
    unfold normRound; cbn [evalLetExpr]. rewrite (clz_eval (f + 3) (e + 3) wsig ltac:(lia) ltac:(lia)), HL.
    replace (f + 3 - 1 - (f + 2)) with 0 by lia.
    cbn [evalExpr]. cbn [fold_left map evalAndBinary evalOrBinary evalBinary KindCustomInd InvDefault getDefault].
    assert (Hz : evalExpr (isZero (Var type (Bit (f + 3)) wsig)) = false).
    { cbn [evalExpr isZero isEq KindCustomInd getDefault].
      destruct (Zmod.eqb_spec wsig Zmod.zero) as [E | E]; [| reflexivity].
      rewrite E, Zmod.unsigned_0 in Hw. pose proof (Z.pow_pos_nonneg 2 (f + 2)); lia. }
    rewrite Hz; cbn [andb].
    rewrite Zmod.unsigned_of_Z, Z.mod_0_l by (apply Z.pow_nonzero; lia).
    assert (Hs0 : Zmod.slu wsig 0 = wsig)
      by (apply Zmod.unsigned_inj; rewrite bits.unsigned_slu, Z.shiftl_0_r; apply Z.mod_small; lia).
    rewrite Hs0. replace (f + 3 - (f + 3)) with 0 by lia.
    apply f_equal. f_equal.
    - rewrite (sub_eval (e + 3) ltac:(lia)); cbn [evalExpr]. rewrite Zmod.of_Z_0, Zmod.sub_0_r; reflexivity.
    - apply Zmod.unsigned_inj. rewrite unsigned_trunc by lia. cbn [evalExpr cst].
      rewrite (Zmod.unsigned_of_Z 0), Z.mod_0_l by (apply Z.pow_nonzero; lia).
      rewrite tz_sru by lia. rewrite Z.pow_0_r, Z.div_1_r. apply Z.mod_small; lia.
    - cbn [evalExpr orb]. rewrite evalExpr_isNotZero_bits.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd cst].
      rewrite unsigned_and_m1_l by lia. rewrite bits.unsigned_and. change (2 ^ 0 - 1) with 0.
      rewrite (Zmod.unsigned_of_Z 0), Z.mod_0_l, Z.land_0_r by (apply Z.pow_nonzero; lia).
      destruct st; reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * One step of the loop
   * --------------------------------------------------------------------------- *)

  Local Abbreviation SK := (SqrtStateK e f).

  Local Abbreviation radOf := (fun st : type SK => st.(Snd).(Fst)).
  Local Abbreviation remOf := (fun st : type SK => st.(Snd).(Snd).(Fst)).
  Local Abbreviation rootOf := (fun st : type SK => st.(Snd).(Snd).(Snd).(Fst)).

  (* `sqrtStep`, transcribed. *)
  Definition top2V (st : type SK) : bits (f + 5) :=
    evalExpr (trunc (2 * f + 6) (f + 5) (Srl (Var type (Bit (2 * f + 6)) (radOf st)) (cst (2 * f + 6) (2 * f + 4)))).
  Definition remSV (st : type SK) : bits (f + 5) :=
    evalExpr (Or [Sll (Var type (Bit (f + 5)) (remOf st)) (cst (f + 5) 2); Var type (Bit (f + 5)) (top2V st)]).
  Definition trialV (st : type SK) : bits (f + 5) :=
    evalExpr (Or [Sll (zext (f + 3) (f + 5) (Var type (Bit (f + 3)) (rootOf st))) (cst (f + 5) 2); cst (f + 5) 1]).
  Definition geV (st : type SK) : bool := negb (Zmod.unsigned (remSV st) <? Zmod.unsigned (trialV st)).

  Definition stepV (st : type SK) : type SK :=
    (st.(Fst) ,, (Zmod.slu (radOf st) (Zmod.unsigned (evalExpr (cst (2 * f + 6) 2))) ,,
     ((if geV st then evalExpr (Sub (Var type (Bit (f + 5)) (remSV st)) (Var type (Bit (f + 5)) (trialV st))) else remSV st) ,,
      (evalExpr (Or [Sll (Var type (Bit (f + 3)) (rootOf st)) (cst (f + 3) 1);
                     ITE (Var type Bool (geV st)) (cst (f + 3) 1) (cst (f + 3) 0)]) ,, st.(Snd).(Snd).(Snd).(Snd))))).

  Lemma sqrtStep_V : forall st, evalLetExpr (sqrtStep e f type st) = stepV st.
  Proof. intros; exact eq_refl. Qed.

  Lemma or2_val : forall w (a b : Expr type (Bit w)),
    Zmod.to_Z (evalExpr (Or [a; b])) = Z.lor (Zmod.to_Z (evalExpr a)) (Zmod.to_Z (evalExpr b)).
  Proof.
    intros; cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
    rewrite !bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l; reflexivity.
  Qed.

  Lemma pf_facts : 4 <= 2 ^ f /\ 2 ^ (f + 1) = 2 * 2 ^ f /\ 2 ^ (f + 2) = 4 * 2 ^ f /\ 2 ^ (f + 3) = 8 * 2 ^ f /\
    2 ^ (f + 5) = 32 * 2 ^ f /\ 2 ^ (2 * f + 4) = 2 ^ (f + 2) * 2 ^ (f + 2) /\ 2 ^ (2 * f + 6) = 4 * 2 ^ (2 * f + 4) /\ 2 * f + 6 < 2 ^ (2 * f + 4).
  Proof.
    assert (2 * f + 6 < 2 ^ (2 * f + 4)).
    { assert (2 * f + 2 < 2 ^ (2 * f + 2)) by (apply Z.pow_gt_lin_r; lia).
      replace (2 * f + 4) with ((2 * f + 2) + 2) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 2) with 4. lia. }
    assert (4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (E : forall k, 0 <= k -> 2 ^ (f + k) = 2 ^ k * 2 ^ f) by (intros; rewrite Z.pow_add_r by lia; lia).
    rewrite !E by lia. change (2 ^ 1) with 2; change (2 ^ 2) with 4; change (2 ^ 3) with 8; change (2 ^ 5) with 32.
    assert (E2 : forall k, 0 <= k -> 2 ^ (2 * f + k) = 2 ^ k * (2 ^ f * 2 ^ f))
      by (intros; replace (2 * f + k) with (k + (f + f)) by lia; rewrite !Z.pow_add_r by lia; lia).
    rewrite !E2 in * by lia. change (2 ^ 4) with 16 in *; change (2 ^ 6) with 64.
    repeat split; try lia; ring.
  Qed.

  Section Step.
    Variable st : type SK.
    Variables R m q : Z.
    Hypothesis HR : Zmod.to_Z (radOf st) = R.
    Hypothesis HMm : Zmod.to_Z (remOf st) = m.
    Hypothesis HQ : Zmod.to_Z (rootOf st) = q.
    Hypothesis Hm : 0 <= m <= 2 * q.
    Hypothesis Hq : q < 2 ^ (f + 2).

    Lemma R_range : 0 <= R < 2 ^ (2 * f + 6).
    Proof. rewrite <- HR; apply bits.unsigned_range; lia. Qed.

    Lemma top2_val : Zmod.to_Z (top2V st) = R / 2 ^ (2 * f + 4).
    Proof.
      pose proof R_range; pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
      assert (0 <= R / 2 ^ (2 * f + 4) < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      unfold top2V; rewrite unsigned_trunc by lia; cbn [evalExpr cst].
      rewrite (tz_ofZ (2 * f + 6) (2 * f + 4)) by lia. rewrite tz_sru by lia. rewrite HR. apply Z.mod_small; lia.
    Qed.

    Lemma remS_val : Zmod.to_Z (remSV st) = 4 * m + R / 2 ^ (2 * f + 4).
    Proof.
      pose proof R_range; pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
      assert (0 <= R / 2 ^ (2 * f + 4) < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      unfold remSV; rewrite or2_val; cbn [evalExpr cst]. rewrite top2_val, bits.unsigned_slu, (tz_ofZ (f + 5) 2) by lia.
      rewrite HMm, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite Z.mod_small by lia. rewrite lor_mul4 by lia; lia.
    Qed.

    Lemma trial_val : Zmod.to_Z (trialV st) = 4 * q + 1.
    Proof.
      pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
      unfold trialV; rewrite or2_val; cbn [evalExpr cst]. rewrite bits.unsigned_slu, unsigned_zext, (tz_ofZ (f + 5) 2), (tz_ofZ (f + 5) 1) by lia.
      cbn [evalExpr cst]. rewrite HQ, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite Z.mod_small by lia. rewrite lor_mul4 by lia; lia.
    Qed.

    Lemma step_val :
      let rS := 4 * m + R / 2 ^ (2 * f + 4) in let ge := 4 * q + 1 <=? rS in
      (stepV st).(Fst) = st.(Fst) /\
      Zmod.to_Z (radOf (stepV st)) = (R * 4) mod 2 ^ (2 * f + 6) /\
      Zmod.to_Z (remOf (stepV st)) = (if ge then rS - (4 * q + 1) else rS) /\
      Zmod.to_Z (rootOf (stepV st)) = 2 * q + b2z ge.
    Proof.
      intros rS ge. pose proof R_range; pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
      assert (0 <= R / 2 ^ (2 * f + 4) < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      assert (Hge : geV st = ge) by (unfold geV, ge; rewrite remS_val, trial_val; fold rS; destruct (Z.ltb_spec rS (4 * q + 1)); destruct (Z.leb_spec (4 * q + 1) rS); try lia; reflexivity).
      unfold stepV; cbn [Fst Snd]. rewrite Hge. split; [reflexivity |]. split; [| split].
      - cbn [evalExpr cst]. rewrite bits.unsigned_slu, (tz_ofZ (2 * f + 6) 2) by lia. rewrite HR, Z.shiftl_mul_pow2 by lia; reflexivity.
      - destruct ge eqn:Eg.
        + rewrite (sub_eval (f + 5) ltac:(lia)); cbn [evalExpr]. rewrite Zmod.unsigned_sub, remS_val, trial_val. fold rS.
          apply Z.leb_le in Eg. apply Z.mod_small; lia.
        + rewrite remS_val; reflexivity.
      - rewrite or2_val; cbn [evalExpr cst]. rewrite bits.unsigned_slu, (tz_ofZ (f + 3) 1) by lia.
        rewrite HQ, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mod_small by lia.
        destruct ge; cbn [evalExpr b2z cst]; rewrite (tz_ofZ (f + 3)) by lia; rewrite lor_mul2 by lia; lia.
    Qed.
  End Step.

  (* ---------------------------------------------------------------------------
   * The loop invariant
   * --------------------------------------------------------------------------- *)

  Section Iter.
    Variable R0 : Z.
    Hypothesis HR0 : 0 <= R0 < 2 ^ (2 * f + 6).

    (* `n` steps remain: `rad` holds the unconsumed low `2 n` radicand bits at its top, and
     * `root` / `rem` are the integer square root / remainder of the consumed prefix. *)
    Definition Inv (n : Z) (st : type SK) : Prop :=
      0 <= n <= f + 3 /\
      Zmod.to_Z (radOf st) = (R0 mod 2 ^ (2 * n)) * 2 ^ (2 * f + 6 - 2 * n) /\
      Zmod.to_Z (rootOf st) * Zmod.to_Z (rootOf st) + Zmod.to_Z (remOf st) = R0 / 2 ^ (2 * n) /\
      0 <= Zmod.to_Z (remOf st) <= 2 * Zmod.to_Z (rootOf st).

    Lemma inv_step : forall n st, 1 <= n -> Inv n st -> Inv (n - 1) (stepV st) /\ (stepV st).(Fst) = st.(Fst).
    Proof.
      intros n st Hn (Hn3 & HR & HP & Hm).
      pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
      set (R := Zmod.to_Z (radOf st)) in *. set (m := Zmod.to_Z (remOf st)) in *. set (q := Zmod.to_Z (rootOf st)) in *.
      set (A := 2 ^ (2 * (n - 1))). set (B := 2 ^ (2 * f + 6 - 2 * n)).
      assert (HA0 : 0 < A) by (apply Z.pow_pos_nonneg; lia).
      assert (HB0 : 0 < B) by (apply Z.pow_pos_nonneg; lia).
      assert (HA4 : 2 ^ (2 * n) = A * 4) by (unfold A; replace (2 * n) with (2 * (n - 1) + 2) by lia; rewrite Z.pow_add_r by lia; reflexivity).
      assert (HAB : A * B = 2 ^ (2 * f + 4)) by (unfold A, B; rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (HB4 : 2 ^ (2 * f + 6 - 2 * (n - 1)) = B * 4)
        by (unfold B; replace (2 * f + 6 - 2 * (n - 1)) with ((2 * f + 6 - 2 * n) + 2) by lia; rewrite Z.pow_add_r by lia; reflexivity).
      (* q is below 2^(f+2) *)
      assert (HPb : R0 / 2 ^ (2 * n) < B).
      { apply Z.div_lt_upper_bound; [lia |]. rewrite HA4. assert (A * 4 * B = 2 ^ (2 * f + 6)) by lia. lia. }
      assert (HBle : B <= 2 ^ (2 * f + 4)) by (unfold B; apply Z.pow_le_mono_r; lia).
      assert (Hq0 : 0 <= q) by lia.
      assert (Hq : q < 2 ^ (f + 2)).
      { destruct (Z_lt_le_dec q (2 ^ (f + 2))) as [H | H]; [exact H |].
        assert (2 ^ (f + 2) * 2 ^ (f + 2) <= q * q) by (apply Z.mul_le_mono_nonneg; lia). lia. }
      (* split the low part *)
      set (a := R0 / A). set (lo := R0 mod A). set (t := a mod 4). set (a4 := a / 4).
      assert (Hlo : 0 <= lo < A) by (apply Z.mod_pos_bound; lia).
      assert (Ht : 0 <= t < 4) by (apply Z.mod_pos_bound; lia).
      assert (Ha : a = 4 * a4 + t) by (apply Z.div_mod; lia).
      assert (Hmod : R0 mod 2 ^ (2 * n) = lo + A * t) by (rewrite HA4, Z.rem_mul_r by lia; reflexivity).
      assert (Hdiv : R0 / 2 ^ (2 * n) = a4) by (rewrite HA4, <- Z.div_div by lia; reflexivity).
      rewrite Hmod in HR. rewrite Hdiv in HP.
      assert (HloB : 0 <= lo * B < A * B) by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_lt_mono_pos_r]; lia).
      assert (HR' : R = 2 ^ (2 * f + 4) * t + lo * B). { rewrite HR, <- HAB. unfold B. ring. }
      assert (Ht2 : R / 2 ^ (2 * f + 4) = t) by (symmetry; apply (Z.div_unique R (2 ^ (2 * f + 4)) t (lo * B)); lia).
      destruct (step_val st R m q eq_refl eq_refl eq_refl Hm Hq) as (S1 & S2 & S3 & S4).
      rewrite Ht2 in S3, S4.
      destruct (isqrt_step a4 q m t HP Hm Ht) as [I1 I2].
      split; [| exact S1].
      split; [lia |]. split; [| split].
      - rewrite S2. replace (2 * (n - 1)) with (2 * (n - 1)) by reflexivity. fold A. fold lo. rewrite HB4.
        rewrite HR'. replace ((2 ^ (2 * f + 4) * t + lo * B) * 4) with (lo * B * 4 + t * (4 * 2 ^ (2 * f + 4))) by ring.
        rewrite <- P26, Z.mod_add by lia. rewrite Z.mod_small; [ring |]. split; [lia |]. rewrite P26. lia.
      - rewrite S3, S4. fold A a. rewrite Ha. exact I1.
      - rewrite S3, S4. exact I2.
    Qed.

    Lemma iter_inv : forall (n : nat) st, Inv (Z.of_nat n) st ->
      Inv 0 (evalLetExpr (sqrtIter e f type n st)) /\ (evalLetExpr (sqrtIter e f type n st)).(Fst) = st.(Fst).
    Proof.
      induction n as [| n IH]; intros st H; [split; [exact H | reflexivity] |].
      cbn [sqrtIter evalLetExpr]. rewrite sqrtStep_V.
      destruct (inv_step (Z.of_nat (S n)) st ltac:(lia) H) as [H1 H2].
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in H1 by lia.
      destruct (IH _ H1) as [I1 I2]. split; [exact I1 | rewrite I2; exact H2].
    Qed.
  End Iter.

  (* ---------------------------------------------------------------------------
   * Small facts
   * --------------------------------------------------------------------------- *)

  Lemma mkFlags_eval : forall nv dz ov uf nx,
    evalExpr (mkFlags type (ConstBool nv) (ConstBool dz) (ConstBool ov) (ConstBool uf) (ConstBool nx)) = mkFl nv dz ov uf nx.
  Proof. intros [] [] [] [] []; reflexivity. Qed.

  Lemma noFl : Zmod.of_Z (2 ^ 5) 0 = mkFl false false false false false.
  Proof. reflexivity. Qed.

  Lemma Bsqrt_pos : forall md (x : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))),
    BinarySingleNaN.is_finite x = true -> BinarySingleNaN.Bsign x = false ->
    BinarySingleNaN.is_finite (BinarySingleNaN.Bsqrt md x) = true /\ BinarySingleNaN.Bsign (BinarySingleNaN.Bsqrt md x) = false.
  Proof.
    intros md x Hx Hs. destruct (@BinarySingleNaN.Bsqrt_correct _ _ _ _ md x) as (_ & B2 & B3).
    destruct x as [s0 | s0 | | s0 m0 x0 Hb]; cbn in Hx, Hs; try discriminate; subst s0.
    - split; reflexivity.
    - rewrite B2; split; [reflexivity |]. rewrite B3; [reflexivity |].
      destruct (BinarySingleNaN.Bsqrt md _) in B2 |- *; first [reflexivity | discriminate].
  Qed.

  (* The rounding window of the square root: `R0 = q^2 + m` locates `sqrt R0` at `q`. *)
  Lemma sqrt_loc : forall R0 q m ex, 0 < R0 -> q * q + m = R0 -> 0 <= m <= 2 * q ->
    inbetween_float radix2 q ex (sqrt (F2R (Float radix2 R0 (2 * ex))))
      (if m =? 0 then loc_Exact else loc_Inexact (if m <=? q then Lt else Gt)).
  Proof.
    intros R0 q m ex HR HP Hm.
    pose proof (Fsqrt_core_correct radix2 R0 (2 * ex) ex HR ltac:(lia)) as H.
    unfold Fsqrt_core in H. replace (2 * ex - 2 * ex) with 0 in H by lia. change (Zpower radix2 0) with 1 in H.
    rewrite Z.mul_1_r in H.
    assert (Hs : Z.sqrtrem R0 = (q, m)).
    { pose proof (Z.sqrtrem_spec R0 ltac:(lia)) as Hsp. destruct (Z.sqrtrem R0) as [q' r'].
      destruct Hsp as [H1 H2].
      assert (Hq : Z.sqrt R0 = q) by (apply Z.sqrt_unique; nia).
      assert (Hq' : Z.sqrt R0 = q') by (apply Z.sqrt_unique; nia).
      assert (q' = q) by lia; subst q'. f_equal; lia. }
    rewrite Hs in H. exact H.
  Qed.

  (* ---------------------------------------------------------------------------
   * A positive finite non-zero operand
   * --------------------------------------------------------------------------- *)

  Lemma sqrt_main : forall rm (a : bits W) E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z a = b2z false * 2 ^ (f + e) + E * 2 ^ f + M -> E <> 2 ^ e - 1 -> (E <> 0 \/ M <> 0) ->
    forall (root : bits (f + 3)) (rem : bits (f + 5)),
    Zmod.to_Z root * Zmod.to_Z root + Zmod.to_Z rem =
      Zmod.to_Z (uSig (unp a)) * 2 ^ (f + 4 + b2z (Z.odd (Zmod.signed (uExp (unp a))))) ->
    0 <= Zmod.to_Z rem <= 2 * Zmod.to_Z root ->
    let o := evalLetExpr (normRound false e f type (f + 3) false
               (evalExpr (Sra (Add [Var type (Bit (e + 3)) (uExp (unp a)); cst (e + 3) (expOff false e)]) (cst 1 1)))
               root (evalExpr (isNotZero (Var type (Bit (f + 5)) rem))) rm) in
    o.(Fst) = ofB (BinarySingleNaN.Bsqrt (modeOf rm) (toB a)) /\
    o.(Snd).(Fst) = finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) (sqrt (BinarySingleNaN.B2R (toB a))).
  Proof.
    intros rm a E M HM HE Ha Hn Hz root rem HP Hm o. pose proof He0.
    pose proof (fin_facts e f Hf Hpe a false E M HM HE Ha Hn Hz) as FF; cbv zeta beta in FF.
    destruct FF as (HS & HX & HV & Hfin & Hsg).
    set (Xa := Zmod.signed (uExp (unp a))) in *. set (Sg := Zmod.to_Z (uSig (unp a))) in *.
    set (q := Zmod.to_Z root) in *. set (m := Zmod.to_Z rem) in *.
    set (R0 := Sg * 2 ^ (f + 4 + b2z (Z.odd Xa))) in *.
    pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
    assert (HR0 : 2 ^ (2 * f + 4) <= R0 < 2 ^ (2 * f + 6)).
    { unfold R0. set (k := f + 4 + b2z (Z.odd Xa)).
      assert (Hk : f + 4 <= k <= f + 5) by (unfold k; destruct (Z.odd Xa); cbn [b2z]; lia).
      assert (Hk0 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
      assert (L : 2 ^ f * 2 ^ k <= Sg * 2 ^ k) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (U : Sg * 2 ^ k < 2 ^ (f + 1) * 2 ^ k) by (apply Z.mul_lt_mono_pos_r; lia).
      rewrite <- Z.pow_add_r in L, U by lia.
      assert (2 ^ (2 * f + 4) <= 2 ^ (f + k)) by (apply Z.pow_le_mono_r; lia).
      assert (2 ^ (f + 1 + k) <= 2 ^ (2 * f + 6)) by (apply Z.pow_le_mono_r; lia).
      lia. }
    assert (Hq : 2 ^ (f + 2) <= q < 2 ^ (f + 3)).
    { assert (Hq0 : 0 <= q) by (apply bits.unsigned_range; lia). split.
      - destruct (Z_lt_le_dec q (2 ^ (f + 2))) as [H1 | H1]; [| exact H1].
        assert ((q + 1) * (q + 1) <= 2 ^ (f + 2) * 2 ^ (f + 2)) by (apply Z.mul_le_mono_nonneg; lia). nia.
      - destruct (Z_lt_le_dec q (2 ^ (f + 3))) as [H1 | H1]; [exact H1 |].
        assert (2 ^ (f + 3) * 2 ^ (f + 3) <= q * q) by (apply Z.mul_le_mono_nonneg; lia).
        assert (2 ^ (2 * f + 6) = 2 ^ (f + 3) * 2 ^ (f + 3)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
    unfold o. rewrite normRound_f3 by lia.
    pose proof (roundPack_Z e f He0 Hf Hpe false
      (evalExpr (Sra (Add [Var type (Bit (e + 3)) (uExp (unp a)); cst (e + 3) (expOff false e)]) (cst 1 1)))
      root (evalExpr (isNotZero (Var type (Bit (f + 5)) rem))) rm) as RP; cbv zeta in RP.
    rewrite RP; cbn [Fst Snd]; clear RP.
    rewrite xr_val, evalExpr_isNotZero_bits, evalExpr_Var. fold Xa q m.
    set (X := Xa / 2). set (st := negb (m =? 0)). set (v := sqrt (BinarySingleNaN.B2R (toB a))).
    set (l0 := if m =? 0 then loc_Exact else loc_Inexact (if m <=? q then Lt else Gt)).
    assert (Hval : BinarySingleNaN.B2R (toB a) = F2R (Float radix2 R0 (2 * (X - f - 2)))).
    { rewrite HV; cbn [cond_Ropp]. unfold R0.
      assert (Ho : Xa mod 2 = b2z (Z.odd Xa)) by (rewrite Zmod_odd; destruct (Z.odd Xa); reflexivity).
      assert (Hd : Xa = 2 * X + Xa mod 2) by (apply Z.div_mod; lia).
      assert (0 <= b2z (Z.odd Xa) <= 1) by (destruct (Z.odd Xa); cbn; lia).
      rewrite <- (F2R_scale Sg (f + 4 + b2z (Z.odd Xa)) (Xa - f)) by lia. f_equal; f_equal; lia. }
    assert (Hv0 : (0 <= v)%R) by apply sqrt_pos.
    assert (Hin : inbetween_float radix2 q (X - f - 2) (Rabs v) l0).
    { rewrite Rabs_pos_eq by exact Hv0. unfold v; rewrite Hval. apply sqrt_loc; [| exact HP | exact Hm].
      pose proof (Z.pow_pos_nonneg 2 (2 * f + 4)); lia. }
    assert (Hs : Rlt_bool v 0 = false) by (apply Rlt_bool_false; exact Hv0).
    assert (Hl0 : l0 = loc_Exact <-> st = false) by (unfold l0, st; destruct (Z.eqb_spec m 0); cbn; split; congruence).
    assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)); change (2 ^ 3) with 8 in *; lia).
    split.
    - destruct (@BinarySingleNaN.Bsqrt_correct _ _ _ _ (modeOf rm) (toB a)) as (B1 & _ & _).
      destruct (Bsqrt_pos (modeOf rm) (toB a) Hfin Hsg) as [F1 F2].
      assert (RR : toB (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) false X q st)) = BinarySingleNaN.Bsqrt (modeOf rm) (toB a)).
      { apply (rp_result e f Hf Hpe (Zmod.to_Z rm) false X q st v l0 Hrm Hq Hin Hl0 Hs).
        change (modeZ (Zmod.to_Z rm)) with (modeOf rm). fold v in B1.
        rewrite Rlt_bool_true; [split; [exact B1 | split; [exact F1 | exact F2]] |].
        rewrite <- B1. apply BinarySingleNaN.abs_B2R_lt_emax. }
      rewrite <- RR. symmetry; apply ofB_toB. rewrite RR.
      destruct (BinarySingleNaN.Bsqrt (modeOf rm) (toB a)); cbn in F1 |- *; congruence.
    - unfold finiteFlags. change (modeOf rm) with (modeZ (Zmod.to_Z rm)). fold v.
      rewrite (rp_flags e f Hf Hpe (Zmod.to_Z rm) false X q st v l0 Hrm Hq Hin Hl0 Hs). reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * The theorem
   * --------------------------------------------------------------------------- *)

  Lemma init_rad_val : forall rm a,
    Zmod.to_Z (radOf (initS rm a)) = Zmod.to_Z (uSig (unp a)) * 2 ^ (f + 4 + b2z (Z.odd (Zmod.signed (uExp (unp a))))).
  Proof.
    intros rm a. pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
    pose proof (bits.unsigned_range (uSig (unp a)) ltac:(lia)) as HS.
    cbn beta. rewrite initS_rad. cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr].
    rewrite oddV_val. set (Sg := Zmod.to_Z (uSig (unp a))) in *.
    assert (E6 : 2 ^ (2 * f + 6) = 2 ^ (f + 1) * 2 ^ (f + 5)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (E5 : 2 ^ (f + 5) = 2 * 2 ^ (f + 4)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (0 < 2 ^ (f + 4)) by (apply Z.pow_pos_nonneg; lia).
    assert (Sg * 2 ^ (f + 5) < 2 ^ (2 * f + 6)) by (rewrite E6; apply Z.mul_lt_mono_pos_r; lia).
    destruct (Z.odd _); cbn [b2z cst evalExpr]; rewrite (tz_ofZ (2 * f + 6)) by lia;
      rewrite Z.shiftl_mul_pow2 by lia; [replace (f + 4 + 1) with (f + 5) by lia | rewrite Z.add_0_r];
      apply Z.mod_small; lia.
  Qed.

  Theorem fsqrt_flocq_ok : fsqrt_flocq.
  Proof.
    intros rm a. rewrite fsqrt_core_res, fsqrt_core_flags. unfold sqrtCore.
    pose proof He0. pose proof pf_facts as (F4 & P1 & P2 & P3 & P5 & P24 & P26 & PL).
    destruct (split_fields e f Hf Hpe a) as (s & E & M & HM & HE & Ha).
    set (R0 := Zmod.to_Z (radOf (initS rm a))).
    assert (HR0 : 0 <= R0 < 2 ^ (2 * f + 6)) by (apply bits.unsigned_range; lia).
    assert (Hinv : Inv R0 (Z.of_nat (sqrtSteps f)) (initS rm a)).
    { unfold sqrtSteps, Inv; rewrite Z2Nat.id by lia. rewrite initS_rem, initS_root, !Zmod.unsigned_of_Z, !Z.mod_0_l
        by (apply Z.pow_nonzero; lia).
      replace (2 * (f + 3)) with (2 * f + 6) by lia. rewrite Z.sub_diag, Z.pow_0_r, Z.mul_1_r, Z.mod_small, Z.div_small by lia.
      fold R0. lia. }
    destruct (iter_inv R0 HR0 _ _ Hinv) as [Hfin Hinfo].
    set (sn := evalLetExpr (sqrtIter e f type (sqrtSteps f) (initS rm a))) in *.
    rewrite sqrtFinish_V. unfold finV. rewrite Hinfo, initS_info. cbn [Fst Snd].
    rewrite (u_nan e f He0 Hf a s E M HM HE Ha), (u_zero e f He0 Hf a s E M HM HE Ha),
            (u_sign e f He0 Hf a s E M HM HE Ha), (u_inf e f He0 Hf a s E M HM HE Ha).
    pose proof (cls e f Hf Hpe a s E M HM HE Ha) as C.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    destruct (Z.eqb_spec E (2 ^ e - 1)) as [HEm | HEm]; destruct (Z.eqb_spec M 0) as [HM0 | HM0];
      destruct (Z.eqb_spec E 0) as [HE0 | HE0]; try (exfalso; lia); cbn [andb negb].
    - (* infinity *)
      unfold sqrtFlags. destruct s.
      + rewrite mkFlags_eval. destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia).
        destruct C as (C1 & _); subst s1; cbn [BinarySingleNaN.Bsqrt]. rewrite (ofB_nan e f Hf Hpe); split; reflexivity.
      + destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia).
        destruct C as (C1 & _); subst s1; cbn [BinarySingleNaN.Bsqrt]. rewrite <- Hb, (ofB_toB e f Hf Hpe a) by (rewrite Hb; reflexivity).
        split; reflexivity.
    - (* NaN *)
      unfold sqrtFlags. rewrite (u_snan e f He0 Hf a s E M HM HE Ha), mkFlags_eval, (isSNaN_eq e f Hf Hpe a s E M HM HE Ha).
      destruct (toB a) eqn:Hb; cbn [clsP] in C; try (exfalso; lia).
      cbn [BinarySingleNaN.Bsqrt]. rewrite (ofB_nan e f Hf Hpe); split; reflexivity.
    - (* zero *)
      unfold sqrtFlags. destruct (toB a) eqn:Hb; cbn [clsP] in C; try (exfalso; lia).
      cbn [BinarySingleNaN.Bsqrt]. rewrite <- Hb, (ofB_toB e f Hf Hpe a) by (rewrite Hb; reflexivity). split; reflexivity.
    - (* finite, M = 0 *)
      assert (Hz : E <> 0 \/ M <> 0) by lia; destruct s;
      [ unfold sqrtFlags; rewrite mkFlags_eval;
        destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia);
        destruct C as (C1 & _); subst s1; cbn [BinarySingleNaN.Bsqrt]; rewrite (ofB_nan e f Hf Hpe); split; reflexivity
      | unfold Inv in Hfin; destruct Hfin as (_ & _ & HP & Hm);
        rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r in HP; unfold R0 in HP; rewrite init_rad_val in HP;
        pose proof (sqrt_main rm a E M HM HE Ha HEm Hz (rootOf sn) (remOf sn) HP Hm) as RR; cbv zeta in RR;
        destruct RR as [R1 R2]; split; [exact R1 |]; etransitivity; [exact R2 |];
        unfold sqrtFlags; destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia);
        destruct C as (C1 & _); subst s1; reflexivity ].
    - (* finite, E = 0 *)
      assert (Hz : E <> 0 \/ M <> 0) by lia; destruct s;
      [ unfold sqrtFlags; rewrite mkFlags_eval;
        destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia);
        destruct C as (C1 & _); subst s1; cbn [BinarySingleNaN.Bsqrt]; rewrite (ofB_nan e f Hf Hpe); split; reflexivity
      | unfold Inv in Hfin; destruct Hfin as (_ & _ & HP & Hm);
        rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r in HP; unfold R0 in HP; rewrite init_rad_val in HP;
        pose proof (sqrt_main rm a E M HM HE Ha HEm Hz (rootOf sn) (remOf sn) HP Hm) as RR; cbv zeta in RR;
        destruct RR as [R1 R2]; split; [exact R1 |]; etransitivity; [exact R2 |];
        unfold sqrtFlags; destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia);
        destruct C as (C1 & _); subst s1; reflexivity ].
    - (* finite, E and M non-zero *)
      assert (Hz : E <> 0 \/ M <> 0) by lia; destruct s;
      [ unfold sqrtFlags; rewrite mkFlags_eval;
        destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia);
        destruct C as (C1 & _); subst s1; cbn [BinarySingleNaN.Bsqrt]; rewrite (ofB_nan e f Hf Hpe); split; reflexivity
      | unfold Inv in Hfin; destruct Hfin as (_ & _ & HP & Hm);
        rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r in HP; unfold R0 in HP; rewrite init_rad_val in HP;
        pose proof (sqrt_main rm a E M HM HE Ha HEm Hz (rootOf sn) (remOf sn) HP Hm) as RR; cbv zeta in RR;
        destruct RR as [R1 R2]; split; [exact R1 |]; etransitivity; [exact R2 |];
        unfold sqrtFlags; destruct (toB a) as [s1 | s1 | | s1 m1 x1 B1] eqn:Hb; cbn [clsP] in C; try (exfalso; lia);
        destruct C as (C1 & _); subst s1; reflexivity ].
  Qed.

End Sqrt.
