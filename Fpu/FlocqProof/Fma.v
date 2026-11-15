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
 * FMADD / FMSUB / FNMSUB / FNMADD against Flocq's `Bfma` (`Fma.v`).
 *
 * `ffmaRef negProd negAdd rm a b c` is the reference core (`FpCoreRef.fpuComputeRef`) on a decoded
 * fused multiply-add: FMADD (false, false), FMSUB (false, true), FNMSUB (true, false),
 * FNMADD (true, true).
 * `ffma_flocq`: its result is Flocq's `Bfma` on `(-a or a)`, `b`, `(-c or c)` (in
 * `BinarySingleNaN`, NaN encoded as the RISC-V canonical NaN) and its flags are the IEEE flags of
 * rounding the exact `a * b + c` (`Flags.v`), with NV for a signaling NaN operand, `inf * 0`
 * (even when `c` is a quiet NaN, as RISC-V requires) and `inf - inf`.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack FmaAlign.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Lemma evalLetExpr_LetEx : forall k k' s (le : LetExpr type k') (cont : type k' -> LetExpr type k),
  evalLetExpr (LetEx s le cont) = evalLetExpr (cont (evalLetExpr le)).
Proof. reflexivity. Qed.

Lemma if_impl : forall (b : bool) (P1 Q1 P2 Q2 : Prop), (P1 -> P2) -> (Q1 -> Q2) ->
  (if b then P1 else Q1) -> (if b then P2 else Q2).
Proof. intros [|]; auto. Qed.

Lemma if_elim : forall (b : bool) (P Q R : Prop), (P -> R) -> (Q -> R) -> (if b then P else Q) -> R.
Proof. intros [|]; auto. Qed.

Lemma evalLetExpr_LetEx_v : forall k k' s (le : LetExpr type k') (cont : type k' -> LetExpr type k) v,
  v = evalLetExpr le -> evalLetExpr (LetEx s le cont) = evalLetExpr (cont v).
Proof. intros; subst; reflexivity. Qed.

(* Evaluate the first `LetE` / `LETE` of a `LetExpr`, naming its value `x` (no term duplication). *)
Tactic Notation "peel" ident(x) :=
  lazymatch goal with |- context [evalLetExpr (LetEx ?s ?le ?cont)] =>
    set (x := evalLetExpr le); rewrite (evalLetExpr_LetEx_v _ _ _ _ _ x eq_refl); cbv beta end.

Section Fma.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation toBp := (toBp e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).
  Local Abbreviation bfloat := (BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))).

  Local Instance precGt : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  (* The decoded fused multiply-add (`FpCore.FpOpDK`): the `fma` family flag and its options. *)
  Definition opFma (negProd negAdd : bool) : type FpOpDK :=
    (false ,, (false ,, (true ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (false ,, (false ,, (false ,, (negProd ,, (negAdd ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (false ,, (false ,, (false ,, tt)))))))))))))))))))))).

  Definition reqFma (negProd negAdd : bool) (rm : bits 3) (a b c : bits W) : type (FpReqK e f xlen) :=
    (opFma negProd negAdd ,, (rm ,, (a ,, (b ,, (c ,, (Zmod.zero ,, tt)))))).

  (* The fused multiply-add in the reference core. *)
  Definition ffmaRef (negProd negAdd : bool) (rm : bits 3) (a b c : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqFma negProd negAdd rm a b c)).

  (* Optional negation. *)
  Definition sgnF (n : bool) (x : bfloat) : bfloat := if n then BinarySingleNaN.Bopp x else x.

  Definition isInfF (x : bfloat) : bool :=
    match x with BinarySingleNaN.B754_infinity _ => true | _ => false end.

  Definition isZeroF (x : bfloat) : bool :=
    match x with BinarySingleNaN.B754_zero _ => true | _ => false end.

  (* Signaling NaN: a NaN whose quiet bit (the top fraction bit) is clear. *)
  Definition isSNaN (x : bits W) : bool :=
    match toBp x with
    | Binary.B754_nan _ _ _ pl _ => negb (Z.testbit (Zpos pl) (f - 1))
    | _ => false
    end.

  (* IEEE flags of the fused multiply-add `A * B + C`. *)
  Definition fmaFlagsF (rm : bits 3) (snA snB snC : bool) (A B C : bfloat) : bits 5 :=
    let invP := (isInfF A && isZeroF B) || (isZeroF A && isInfF B) in
    if BinarySingleNaN.is_nan A || BinarySingleNaN.is_nan B || BinarySingleNaN.is_nan C || invP then
      mkFl (snA || snB || snC || invP) false false false false
    else if BinarySingleNaN.is_finite A && BinarySingleNaN.is_finite B && BinarySingleNaN.is_finite C then
      finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
        (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B + BinarySingleNaN.B2R C)%R
    else if (isInfF A || isInfF B) && isInfF C &&
            negb (Bool.eqb (xorb (BinarySingleNaN.Bsign A) (BinarySingleNaN.Bsign B)) (BinarySingleNaN.Bsign C))
    then mkFl true false false false false
    else mkFl false false false false false.

  Definition fmaFlags (negProd negAdd : bool) (rm : bits 3) (a b c : bits W) : bits 5 :=
    fmaFlagsF rm (isSNaN a) (isSNaN b) (isSNaN c) (sgnF negProd (toB a)) (toB b) (sgnF negAdd (toB c)).

  Definition ffma_flocq : Prop :=
    forall negProd negAdd rm a b c,
      (ffmaRef negProd negAdd rm a b c) @% "res" =
        ofB (BinarySingleNaN.Bfma (modeOf rm) (sgnF negProd (toB a)) (toB b) (sgnF negAdd (toB c))) /\
      (ffmaRef negProd negAdd rm a b c) @% "flags" = fmaFlags negProd negAdd rm a b c.

  (* ---------------------------------------------------------------------------
   * The FMA path of the core
   * --------------------------------------------------------------------------- *)

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation XK := (Bit (e + 3)).
  Local Abbreviation WF := (2 * f + 6).

  Local Abbreviation iRm := (fun (i : type (PipeInfoK e f xlen)) => i.(Snd).(Snd).(Fst)).
  Local Abbreviation iC2 := (fun (i : type (PipeInfoK e f xlen)) => i.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation iUa := (fun (i : type (PipeInfoK e f xlen)) => i.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation iUb := (fun (i : type (PipeInfoK e f xlen)) => i.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation iUc := (fun (i : type (PipeInfoK e f xlen)) => i.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation iNp := (fun (i : type (PipeInfoK e f xlen)) => i.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  Definition flipC (n : bool) (c : bits W) : bits W :=
    evalExpr (flipSign e f type (And [ConstBool true; ConstBool n]) c).

  Local Abbreviation infoOf := (fun np na rm a b c => evalLetExpr (pipeInfoOf false e f xlen type (reqFma np na rm a b c))).

  Lemma core_top_res : forall np na rm a b c, (ffmaRef np na rm a b c) @% "res" =
    (evalLetExpr (pipeSpec false e f xlen wlen type (reqFma np na rm a b c))) @% "res".
  Proof. intros; exact eq_refl. Qed.

  Lemma core_top_flags : forall np na rm a b c, (ffmaRef np na rm a b c) @% "flags" =
    (evalLetExpr (pipeSpec false e f xlen wlen type (reqFma np na rm a b c))) @% "flags".
  Proof. intros; exact eq_refl. Qed.

  Lemma core_pipe : forall req : type (FpReqK e f xlen),
    evalLetExpr (pipeSpec false e f xlen wlen type req) =
    evalLetExpr (pipeFinishCore false e f xlen wlen type (evalLetExpr (pipeInfoOf false e f xlen type req))
       (evalExpr (sigProduct f type (uSig (iUa (evalLetExpr (pipeInfoOf false e f xlen type req))))
                                    (uSig (iUb (evalLetExpr (pipeInfoOf false e f xlen type req))))))).
  Proof. intros. unfold pipeSpec. do 6 (rewrite evalLetExpr_LetEx; cbv beta). reflexivity. Qed.

  Lemma core_fin_res : forall np na (i : type (PipeInfoK e f xlen)) prod, i.(Fst) = opFma np na ->
    (evalLetExpr (pipeFinishCore false e f xlen wlen type i prod)) @% "res" =
    (evalLetExpr (fmaFinish false e f type (iRm i) (iC2 i) (iUa i) (iUb i) (iUc i) (iNp i) prod)).(Fst).
  Proof. intros np na [op i] prod H; cbn [Fst] in H; subst op. exact eq_refl. Qed.

  Lemma core_fin_flags : forall np na (i : type (PipeInfoK e f xlen)) prod, i.(Fst) = opFma np na ->
    (evalLetExpr (pipeFinishCore false e f xlen wlen type i prod)) @% "flags" =
    (evalLetExpr (fmaFinish false e f type (iRm i) (iC2 i) (iUa i) (iUb i) (iUc i) (iNp i) prod)).(Snd).(Fst).
  Proof. intros np na [op i] prod H; cbn [Fst] in H; subst op. exact eq_refl. Qed.

  Lemma info_op : forall np na rm a b c, (infoOf np na rm a b c).(Fst) = opFma np na.
  Proof. intros; exact eq_refl. Qed.
  Lemma info_rm : forall np na rm a b c, iRm (infoOf np na rm a b c) = rm.
  Proof. intros; exact eq_refl. Qed.
  Lemma info_c2 : forall np na rm a b c, iC2 (infoOf np na rm a b c) = flipC na c.
  Proof. intros; exact eq_refl. Qed.
  Lemma info_ua : forall np na rm a b c, iUa (infoOf np na rm a b c) = unp a.
  Proof. intros; exact eq_refl. Qed.
  Lemma info_ub : forall np na rm a b c,
    iUb (infoOf np na rm a b c) = unp (evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) b)).
  Proof. intros; exact eq_refl. Qed.
  Lemma info_uc : forall np na rm a b c, iUc (infoOf np na rm a b c) = unp (flipC na c).
  Proof. intros; exact eq_refl. Qed.
  Lemma info_np : forall np na rm a b c, iNp (infoOf np na rm a b c) = np.
  Proof. intros; exact eq_refl. Qed.

  Lemma HeM : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Lemma flip0 : forall b : bits W, evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) b) = b.
  Proof.
    intros b; pose proof HeM; cbn [evalExpr flipSign fold_left map evalXorBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault andb cst].
    change (Zmod.xor (Zmod.xor Zmod.zero b) (Zmod.of_Z (2 ^ W) 0) = b). apply Zmod.unsigned_inj. rewrite !bits.unsigned_xor, Zmod.unsigned_0, Z.lxor_0_l, Zmod.unsigned_of_Z, Z.mod_0_l, Z.lxor_0_r
      by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.

  Lemma ffma_core : forall np na rm a b c,
    let c2 := flipC na c in
    let prodF := evalExpr (sigProduct f type (uSig (unp a)) (uSig (unp b))) in
    (ffmaRef np na rm a b c) @% "res" = (evalLetExpr (fmaFinish false e f type rm c2 (unp a) (unp b) (unp c2) np prodF)).(Fst) /\
    (ffmaRef np na rm a b c) @% "flags" = (evalLetExpr (fmaFinish false e f type rm c2 (unp a) (unp b) (unp c2) np prodF)).(Snd).(Fst).
  Proof.
    intros np na rm a b c c2 prodF.
    rewrite core_top_res, core_top_flags, !core_pipe.
    rewrite (core_fin_res np na), (core_fin_flags np na) by apply info_op.
    rewrite !info_rm, !info_c2, !info_ua, !info_ub, !info_uc, !info_np, !flip0.
    split; reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * Operand classes (helpers as in `Mul.v`)
   * --------------------------------------------------------------------------- *)

  Local Abbreviation eminF := (SpecFloat.emin (f + 1) (2 ^ (e - 1))).

  Definition clsP (x : bfloat) (s : bool) (E M : Z) : Prop :=
    match x with
    | BinarySingleNaN.B754_zero s' => s' = s /\ E = 0 /\ M = 0
    | BinarySingleNaN.B754_infinity s' => s' = s /\ E = 2 ^ e - 1 /\ M = 0
    | BinarySingleNaN.B754_nan => E = 2 ^ e - 1 /\ M <> 0
    | BinarySingleNaN.B754_finite s' m ex _ =>
        s' = s /\ E <> 2 ^ e - 1 /\ (E <> 0 \/ M <> 0) /\
        Zpos m = (if E =? 0 then M else M + 2 ^ f) /\ ex = (if E =? 0 then eminF else E + eminF - 1)
    end.

  Lemma cls : forall (x : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M -> clsP (toB x) s E M.
  Proof.
    intros x s E M HM HE Hx. pose proof HeM as He0.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    pose proof (B2SF_toB_fields e f Hf Hpe x s E M HM HE Hx) as H.
    destruct (toB x) as [s' | s' | | s' m ex Hb]; cbn [BinarySingleNaN.B2SF clsP] in *; unfold sfFields in H;
      destruct (Z.eqb_spec E 0); destruct (Z.eqb_spec M 0); destruct (Z.eqb_spec E (2 ^ e - 1));
      try discriminate H; try (injection H; intros); subst; repeat split; try lia.
    all: try (rewrite Z2Pos.id by lia; reflexivity).
    all: try (assert (Hp : 0 < M + 2 ^ f) by lia; destruct (M + 2 ^ f); try lia; injection H; intros; subst; reflexivity).
  Qed.

  Lemma isSNaN_eq : forall (x : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    isSNaN x = (E =? 2 ^ e - 1) && negb (M =? 0) && negb (Z.testbit M (f - 1)).
  Proof.
    intros x s E M HM HE Hx. pose proof HeM as He0.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (HA : Binary.B2FF _ _ (toBp x) = binary_float_of_bits_aux f e (b2z s * 2 ^ (f + e) + E * 2 ^ f + M))
      by (unfold Glue.toBp, binary_float_of_bits; rewrite B2FF_FF2B, Hx; reflexivity).
    rewrite <- (join_bits_eq e f Hf Hpe) in HA. unfold binary_float_of_bits_aux in HA. rewrite split_join_bits in HA by lia.
    unfold isSNaN.
    destruct (toBp x) as [s' | s' | s' pl Hpl | s' m ex Hb]; cbn [Binary.B2FF] in HA;
      destruct (Z.eqb_spec E 0); destruct (Z.eqb_spec M 0); destruct (Z.eqb_spec E (2 ^ e - 1));
      cbn [andb negb]; try reflexivity; try lia; try discriminate HA;
      try (destruct M; try lia; discriminate HA);
      try (assert (Hp : 0 < M + 2 ^ f) by lia; destruct (M + 2 ^ f); try lia; discriminate HA).
    destruct M as [| p | p]; try lia. injection HA; intros; subst; reflexivity.
  Qed.

  Lemma ofB_nan : ofB BinarySingleNaN.B754_nan = evalExpr (qnanE e f type).
  Proof.
    pose proof HeM as He0. unfold Glue.ofB; cbn [BSN2B build_nan canonNaN proj1_sig bits_of_binary_float].
    rewrite (join_bits_eq e f Hf Hpe). cbn [Binary.Bsign get_nan_pl b2z]. rewrite Z2Pos.id by (apply Z.pow_pos_nonneg; lia).
    cbn [evalExpr qnanE cst]. unfold qnanMagZ, infMagZ. cbn [b2z]. f_equal; lia.
  Qed.

  Lemma ofB_inf : forall s, ofB (BinarySingleNaN.B754_infinity s) = evalExpr (infE e f type (Var type Bool s)).
  Proof.
    intros s; pose proof HeM as He0. unfold Glue.ofB; cbn [BSN2B bits_of_binary_float].
    rewrite (join_bits_eq e f Hf Hpe).
    assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; lia).
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (Hf1 : 1 <= 2 ^ f) by (pose proof (Z.pow_le_mono_r 2 0 f); lia).
    apply Zmod.unsigned_inj. cbn [evalExpr infE packSigned boolBit cst]. rewrite unsigned_app_arith by lia.
    rewrite (tz_ofZ (f + e)) by (unfold infMagZ; nia).
    assert (HW1 : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    rewrite tz_ofZ by (destruct s; cbn [b2z]; unfold infMagZ in *; nia).
    destruct s; cbn; unfold infMagZ; lia.
  Qed.

  Lemma ofB_zero : forall s, ofB (BinarySingleNaN.B754_zero s) = evalExpr (zeroE e f type (Var type Bool s)).
  Proof.
    intros s; pose proof HeM as He0. unfold Glue.ofB; cbn [BSN2B bits_of_binary_float].
    rewrite (join_bits_eq e f Hf Hpe).
    assert (Hfe : 0 < 2 ^ (f + e)) by (apply Z.pow_pos_nonneg; lia).
    assert (HW1 : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    apply Zmod.unsigned_inj. cbn [evalExpr zeroE packSigned boolBit cst]. rewrite unsigned_app_arith by lia.
    rewrite (tz_ofZ (f + e)) by lia.
    rewrite tz_ofZ by (destruct s; cbn [b2z]; lia).
    destruct s; cbn; lia.
  Qed.

  Lemma prod_val : forall siga sigb : bits (f + 1),
    Zmod.to_Z (evalExpr (sigProduct f type siga sigb)) = Zmod.to_Z siga * Zmod.to_Z sigb.
  Proof.
    intros siga sigb.
    pose proof (bits.unsigned_range siga ltac:(lia)); pose proof (bits.unsigned_range sigb ltac:(lia)).
    unfold sigProduct; cbn [evalExpr fold_left map].
    rewrite !Zmod.unsigned_mul, Zmod.unsigned_1, !unsigned_zext by lia; cbn [evalExpr].
    assert (H2 : 2 ^ (2 * f + 2) = 2 ^ (f + 1) * 2 ^ (f + 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (1 < 2 ^ (2 * f + 2)) by (apply Z.pow_gt_1; lia).
    assert (2 ^ (f + 1) <= 2 ^ (2 * f + 2)) by (apply Z.pow_le_mono_r; lia).
    rewrite (Z.mod_small 1), Z.mul_1_l, (Z.mod_small (Zmod.to_Z siga)) by lia. apply Z.mod_small. split; [nia |].
    rewrite H2. apply Z.mul_lt_mono_nonneg; lia.
  Qed.

  (* The class relation between an unpacked operand and a Flocq float (sign flipped by `n`). *)
  Definition urel (n : bool) (u : type (FpUnpK e f)) (x : bfloat) : Prop :=
    uNaN u = BinarySingleNaN.is_nan x /\ uInf u = isInfF x /\ uZero u = isZeroF x /\
    (BinarySingleNaN.is_nan x = false -> BinarySingleNaN.Bsign x = xorb n (uSign u)) /\
    (BinarySingleNaN.is_finite_strict x = true ->
       2 ^ f <= Zmod.to_Z (uSig u) < 2 ^ (f + 1) /\ fpEmin e - f <= Zmod.signed (uExp u) <= fpEmax e /\
       BinarySingleNaN.B2R x = cond_Ropp (BinarySingleNaN.Bsign x) (F2R (Float radix2 (Zmod.to_Z (uSig u)) (Zmod.signed (uExp u) - f)))).

  Lemma urel_fields : forall (x : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M -> urel false (unp x) (toB x).
  Proof.
    intros x s E M HM HE Hx. pose proof HeM as He0.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    pose proof (u_value e f He0 Hf Hpe x s E M HM HE Hx) as HV.
    pose proof (cls x s E M HM HE Hx) as C.
    unfold urel. rewrite (u_nan e f He0 Hf x s E M HM HE Hx), (u_inf e f He0 Hf x s E M HM HE Hx),
      (u_zero e f He0 Hf x s E M HM HE Hx), (u_sign e f He0 Hf x s E M HM HE Hx).
    destruct (toB x) as [s' | s' | | s' m ex Hb]; cbn [clsP BinarySingleNaN.is_nan isInfF isZeroF
      BinarySingleNaN.Bsign BinarySingleNaN.is_finite_strict xorb] in *.
    - destruct C as (-> & -> & ->). rewrite Z.eqb_refl. replace (0 =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      repeat split; discriminate.
    - destruct C as (-> & -> & ->). rewrite Z.eqb_refl. replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      repeat split; discriminate.
    - destruct C as (-> & HM0). rewrite Z.eqb_refl. replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (M =? 0) with false by (symmetry; apply Z.eqb_neq; lia). repeat split; discriminate.
    - destruct C as (-> & Hn & Hz & Hm & Hex).
      replace (E =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace ((E =? 0) && (M =? 0)) with false by (destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); cbn; lia).
      specialize (HV Hn Hz); cbv zeta in HV; destruct HV as (HS & HX & HV).
      repeat split; try reflexivity; try lia.
      change (BinarySingleNaN.B2R (BinarySingleNaN.B754_finite s m ex Hb)) with (F2R (Float radix2 (cond_Zopp s (Zpos m)) ex)).
      rewrite F2R_cond_Zopp, HV, Hm, Hex; reflexivity.
  Qed.

  Lemma urel_sgn : forall n u x, urel false u x -> urel n u (sgnF n x).
  Proof.
    intros [|] u x H; [| exact H].
    destruct H as (H1 & H2 & H3 & H4 & H5); cbn [sgnF]. unfold urel.
    rewrite BinarySingleNaN.is_nan_Bopp, BinarySingleNaN.is_finite_strict_Bopp.
    split; [exact H1 |]. split; [destruct x; exact H2 |]. split; [destruct x; exact H3 |]. split.
    - intros Hn. rewrite BinarySingleNaN.Bsign_Bopp, H4 by exact Hn. destruct (uSign u); reflexivity.
    - intros Hs. destruct (H5 Hs) as (HS & HX & HV). split; [exact HS |]. split; [exact HX |].
      rewrite BinarySingleNaN.B2R_Bopp, HV, BinarySingleNaN.Bsign_Bopp by (destruct x; try discriminate; reflexivity).
      destruct (BinarySingleNaN.Bsign x); cbn [negb cond_Ropp]; rewrite ?Ropp_involutive; reflexivity.
  Qed.

  Lemma isSNaN_u : forall (x : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M -> isSNaN x = uSNaN (unp x).
  Proof.
    intros x s E M HM HE Hx. rewrite (isSNaN_eq x s E M HM HE Hx), (u_snan e f HeM Hf x s E M HM HE Hx). reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * The sign flip of `c`
   * --------------------------------------------------------------------------- *)

  Lemma land_low_pow : forall k low, 0 <= k -> 0 <= low < 2 ^ k -> Z.land low (2 ^ k) = 0.
  Proof.
    intros k low Hk Hl. apply Z.bits_inj'; intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia. rewrite Z.bits_0.
    destruct (Z.eqb_spec k i) as [<- | _]; [| apply andb_false_r]. rewrite andb_true_r.
    apply Z.testbit_false; [lia |]. rewrite Z.div_small by lia; reflexivity.
  Qed.

  Lemma lxor_top : forall k (s : bool) low, 0 <= k -> 0 <= low < 2 ^ k ->
    Z.lxor (b2z s * 2 ^ k + low) (2 ^ k) = b2z (negb s) * 2 ^ k + low.
  Proof.
    intros k s low Hk Hl. pose proof (land_low_pow k low Hk Hl) as H0.
    destruct s; cbn [b2z negb]; rewrite ?Z.mul_1_l, ?Z.mul_0_l, ?Z.add_0_l.
    - rewrite Z.add_comm, (Z.add_nocarry_lxor low (2 ^ k)) by exact H0.
      rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity.
    - rewrite Z.add_comm; symmetry; apply Z.add_nocarry_lxor; exact H0.
  Qed.

  Lemma flipC_bits : forall n (c : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z c = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    Zmod.to_Z (flipC n c) = b2z (xorb n s) * 2 ^ (f + e) + E * 2 ^ f + M.
  Proof.
    intros n c s E M HM HE Hc. pose proof HeM.
    unfold flipC; cbn [evalExpr flipSign fold_left map evalXorBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault andb cst].
    assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; lia).
    assert (HW1 : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    assert (Hlow : 0 <= E * 2 ^ f + M < 2 ^ (f + e)).
    { assert (E * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
    change (Zmod.to_Z (Zmod.xor (Zmod.xor Zmod.zero c) (if n then Zmod.of_Z (2 ^ W) (2 ^ (f + e)) else Zmod.of_Z (2 ^ W) 0)) =
            b2z (xorb n s) * 2 ^ (f + e) + E * 2 ^ f + M).
    rewrite !bits.unsigned_xor, Zmod.unsigned_0, Z.lxor_0_l, Hc.
    destruct n; cbn [xorb].
    - rewrite Zmod.unsigned_of_Z, (Z.mod_small (2 ^ (f + e))) by lia.
      rewrite <- Z.add_assoc, lxor_top by lia. destruct s; cbn [negb]; lia.
    - rewrite Zmod.unsigned_of_Z, Z.mod_0_l, Z.lxor_0_r by lia. reflexivity.
  Qed.

  Lemma flipC_toB : forall n (c : bits W), toB (flipC n c) = sgnF n (toB c).
  Proof.
    intros n c. destruct (split_fields e f Hf Hpe c) as (s & E & M & HM & HE & Hc).
    pose proof (flipC_bits n c s E M HM HE Hc) as H2.
    pose proof (cls c s E M HM HE Hc) as C1. pose proof (cls (flipC n c) (xorb n s) E M HM HE H2) as C2.
    pose proof HeM. assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    apply B2SF_inj.
    destruct (toB c) as [s1 | s1 | | s1 m1 x1 B1], (toB (flipC n c)) as [s2 | s2 | | s2 m2 x2 B2];
      cbn [clsP] in C1, C2; try lia; destruct n; cbn [sgnF BinarySingleNaN.Bopp BinarySingleNaN.B2SF xorb] in *; try reflexivity.
    all: try (destruct C1 as (-> & _), C2 as (-> & _); reflexivity).
    all: destruct C1 as (-> & _ & _ & Hm1 & Hx1), C2 as (-> & _ & _ & Hm2 & Hx2);
      rewrite <- Hm2 in Hm1; injection Hm1 as ->; subst x1 x2; reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * `alignAdd` on integers
   * --------------------------------------------------------------------------- *)

  Lemma signed_sub_mod : forall (a b : bits (e + 3)),
    Zmod.to_Z (Zmod.sub a b) = (Zmod.signed a - Zmod.signed b) mod 2 ^ (e + 3).
  Proof.
    intros a b. rewrite <- (Zmod.of_Z_signed a), <- (Zmod.of_Z_signed b) at 1.
    rewrite <- Zmod.of_Z_sub, Zmod.unsigned_of_Z. reflexivity.
  Qed.

  Lemma alignAdd_eval : forall W' sB sS (xB xS : bits (e + 3)) (big sm : bits W'), 0 < W' < 2 ^ (e + 2) ->
    exists sh, 0 <= sh <= W' /\
      (0 <= Zmod.signed xB - Zmod.signed xS < 2 ^ (e + 2) -> sh = Z.min (Zmod.signed xB - Zmod.signed xS) W') /\
      (evalLetExpr (alignAdd e type W' sB sS xB xS big sm)).(Snd).(Fst) = negb (Zmod.to_Z sm mod 2 ^ sh =? 0) /\
      (Bool.eqb sB sS = true -> Zmod.to_Z big + Zmod.to_Z sm / 2 ^ sh < 2 ^ W' ->
         Zmod.to_Z (evalLetExpr (alignAdd e type W' sB sS xB xS big sm)).(Fst) = Zmod.to_Z big + Zmod.to_Z sm / 2 ^ sh) /\
      (Bool.eqb sB sS = false -> 0 <= Zmod.to_Z big - Zmod.to_Z sm / 2 ^ sh - b2z (negb (Zmod.to_Z sm mod 2 ^ sh =? 0)) ->
         Zmod.to_Z (evalLetExpr (alignAdd e type W' sB sS xB xS big sm)).(Fst) =
         Zmod.to_Z big - Zmod.to_Z sm / 2 ^ sh - b2z (negb (Zmod.to_Z sm mod 2 ^ sh =? 0))).
  Proof.
    intros W' sB sS xB xS big sm HW. pose proof HeM as He0.
    assert (He3 : 2 ^ (e + 3) = 2 * 2 ^ (e + 2)) by (replace (e + 3) with (Z.succ (e + 2)) by lia; rewrite Z.pow_succ_r by lia; lia).
    assert (Hp2 : 0 < 2 ^ (e + 2)) by (apply Z.pow_pos_nonneg; lia).
    set (D := Zmod.signed xB - Zmod.signed xS).
    set (dz := D mod 2 ^ (e + 3)).
    set (shZ := if dz <? W' then dz else W').
    assert (Hdz : 0 <= dz < 2 ^ (e + 3)) by (apply Z.mod_pos_bound; lia).
    assert (Hsh : 0 <= shZ <= W') by (unfold shZ; destruct (Z.ltb_spec dz W'); lia).
    exists shZ. split; [exact Hsh |]. split.
    { intros HD. unfold shZ, dz. rewrite Z.mod_small by lia. destruct (Z.ltb_spec D W'); lia. }
    pose proof (bits.unsigned_range big ltac:(lia)) as Hbig. pose proof (bits.unsigned_range sm ltac:(lia)) as Hsm.
    assert (HWp : W' < 2 ^ W') by (apply Z.pow_gt_lin_r; lia).
    unfold alignAdd. peel d. peel sh. peel smSh. peel st. peel effSub. peel r.
    change (evalLetExpr (RetE ?x)) with (evalExpr x). cbn [evalExpr mapDiffTuple Fst Snd snd].
    assert (Hd : Zmod.to_Z d = dz) by (unfold d; cbn [evalLetExpr]; rewrite (sub_eval (e + 3) ltac:(lia)); apply signed_sub_mod).
    clearbody d.
    assert (Hshv : Zmod.to_Z sh = shZ).
    { unfold sh; cbn [evalLetExpr evalExpr cst]. rewrite (tz_ofZ (e + 3) W') by lia. rewrite Hd. unfold shZ.
      destruct (dz <? W'); [exact Hd | apply tz_ofZ; lia]. }
    clearbody sh.
    assert (HsmSh : Zmod.to_Z smSh = Zmod.to_Z sm / 2 ^ shZ).
    { unfold smSh; cbn [evalLetExpr evalExpr]. rewrite tz_sru by lia. rewrite Hshv; reflexivity. }
    clearbody smSh.
    assert (Hst : st = negb (Zmod.to_Z sm mod 2 ^ shZ =? 0)).
    { unfold st; cbn [evalLetExpr]. rewrite evalExpr_isNotZero_bits.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd evalNot cst].
      rewrite unsigned_and_m1_l by lia. rewrite (tz_lowmask W' sm (Zmod.to_Z sh)) by lia. rewrite Hshv; reflexivity. }
    clearbody st.
    assert (Hes : effSub = negb (Bool.eqb sB sS)) by (unfold effSub; reflexivity).
    clearbody effSub.
    assert (Hq : 0 <= Zmod.to_Z sm / 2 ^ shZ) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
    split; [exact Hst |]. split.
    - intros Heq Hlt. unfold r; cbn [evalLetExpr evalExpr]. rewrite Hes, Heq; cbn [negb].
      cbn [fold_left map evalExpr]. rewrite !Zmod.unsigned_add, Zmod.unsigned_0, Z.add_0_l, (Z.mod_small (Zmod.to_Z big)) by lia.
      rewrite HsmSh. apply Z.mod_small; lia.
    - intros Heq Hge. unfold r; cbn [evalLetExpr evalExpr]. rewrite Hes, Heq; cbn [negb].
      rewrite !(sub_eval W' ltac:(lia)). cbn [evalExpr cst]. rewrite !Zmod.unsigned_sub, HsmSh, <- Hst. rewrite <- Hst in Hge.
      rewrite (Z.mod_small (Zmod.to_Z big - _)) by (destruct st; cbn [b2z] in *; lia).
      assert (1 < 2 ^ W') by lia.
      destruct st; cbn [b2z] in Hge |- *; rewrite Zmod.unsigned_of_Z.
      + rewrite (Z.mod_small 1) by lia. apply Z.mod_small; lia.
      + rewrite Z.mod_0_l by lia. apply Z.mod_small; lia.
  Qed.

  (* ---------------------------------------------------------------------------
   * Small facts used by the finite path
   * --------------------------------------------------------------------------- *)

  Lemma testbit_top : forall x n, 0 <= n -> 0 <= x < 2 ^ (n + 1) -> Z.testbit x n = (2 ^ n <=? x).
  Proof.
    intros x n Hn Hx.
    assert (H2 : 2 ^ (n + 1) = 2 * 2 ^ n) by (rewrite Z.pow_add_r by lia; lia).
    assert (Hp : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
    replace (Z.testbit x n) with (Z.testbit (Z.shiftr x n) 0) by (rewrite Z.shiftr_spec by lia; f_equal; lia).
    rewrite Z.shiftr_div_pow2, Z.bit0_odd by lia.
    destruct (Z.leb_spec (2 ^ n) x).
    - replace (x / 2 ^ n) with 1 by (apply Z.div_unique with (x - 2 ^ n); lia). reflexivity.
    - rewrite Z.div_small by lia. reflexivity.
  Qed.

  Lemma modeDN : forall rm : bits 3,
    match modeOf rm with mode_DN => true | _ => false end = (Zmod.to_Z rm =? 2).
  Proof.
    intros rm. unfold modeOf. destruct (Zmod.to_Z rm) as [| p | p]; try reflexivity.
    destruct p as [[p | p |] | [p | p |] |]; try reflexivity; destruct p; reflexivity.
  Qed.

  Lemma eqRdn : forall rm : bits 3, evalExpr (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) = (Zmod.to_Z rm =? 2).
  Proof. intros rm; cbn [evalExpr cst]. apply (eqb_ofZ 3); unfold RmRdn; lia. Qed.

  Lemma flags0 : forall m, finiteFlags (f + 1) (2 ^ (e - 1)) m 0%R = mkFl false false false false false.
  Proof.
    intros m. unfold finiteFlags, roundFlags; cbv zeta.
    rewrite (round_0 radix2 (SpecFloat.fexp _ _) (round_mode m)), (round_0 radix2 (FLX_exp _) (round_mode m)).
    rewrite Rabs_R0, Rlt_bool_true by apply bpow_gt_0.
    rewrite Req_bool_true by reflexivity. cbn [negb orb]. rewrite andb_false_r. reflexivity.
  Qed.

  Lemma noFlags_eq : evalExpr (noFlags type) = mkFl false false false false false.
  Proof. reflexivity. Qed.

  Lemma normRound_zero : forall W' s x (wsig : bits W') st rm, Zmod.to_Z wsig = 0 -> st = false ->
    evalLetExpr (normRound false e f type W' s x wsig st rm) =
    (evalExpr (zeroE e f type (Var type Bool s)) ,, (evalExpr (noFlags type) ,, tt)).
  Proof.
    intros W' s x wsig st rm Hw Hs. unfold normRound.
    peel lz. peel sigN. peel xN. peel top. peel st2. peel isZ. peel rp.
    assert (HZ : isZ = true).
    { unfold isZ; cbn [evalLetExpr]. change ((evalExpr (isZero (Var type (Bit W') wsig)) && negb st)%bool = true).
      rewrite (isZero_eval W' wsig), Hw, Hs; reflexivity. }
    clearbody isZ. subst isZ. reflexivity.
  Qed.

  Lemma B2R_cond_Ropp_F2R : forall s m x, cond_Ropp s (F2R (Float radix2 m x)) = F2R (Float radix2 (cond_Zopp s m) x).
  Proof. intros; rewrite F2R_cond_Zopp; reflexivity. Qed.

  (* ---------------------------------------------------------------------------
   * The finite path: alignment and rounding
   * --------------------------------------------------------------------------- *)

  Section Nrm.
    Variables (rm : bits 3) (ua ub uc : type (FpUnpK e f)) (np : bool) (A B C : bfloat).
    Hypothesis HA : urel np ua A.
    Hypothesis HB : urel false ub B.
    Hypothesis HC : urel false uc C.
    Hypothesis HAf : BinarySingleNaN.is_finite_strict A = true.
    Hypothesis HBf : BinarySingleNaN.is_finite_strict B = true.
    Hypothesis HCf : BinarySingleNaN.is_finite C = true.

    Variables (prod pn : bits (2 * f + 2)) (sp sc top xGt xEq pBig sBig sSm st sR : bool)
      (xc xp xBig xSm xR : bits (e + 3)) (pext cext cz big sm r : bits WF) (sigc : bits (f + 1))
      (al : type (AlignK WF)).
    Hypothesis Hprod : prod = evalExpr (sigProduct f type (uSig ua) (uSig ub)).
    Hypothesis Hsp : sp = xorb (xorb (uSign ua) (uSign ub)) np.
    Hypothesis Hsc : sc = uSign uc.
    Hypothesis Hxc : xc = uExp uc.
    Hypothesis Htop : top = evalExpr (bitSet (ty := type) prod (2 * f + 1)).
    Hypothesis Hpn : pn = if top then prod else evalExpr (Sll (Var type (Bit (2 * f + 2)) prod) (cst (2 * f + 2) 1)).
    Hypothesis Hxp : xp = evalExpr (Add [Var type XK (uExp ua); Var type XK (uExp ub);
                       ITE (Var type Bool top) (cst (e + 3) (1 - expOff false e)) (cst (e + 3) (0 - expOff false e))]).
    Hypothesis Hpext : pext = evalExpr (Sll (zext (2 * f + 2) WF (Var type (Bit (2 * f + 2)) pn)) (cst WF 3)).
    Hypothesis Hsigc : sigc = uSig uc.
    Hypothesis Hcext : cext = evalExpr (Sll (zext (f + 1) WF (Var type (Bit (f + 1)) sigc)) (cst WF (f + 4))).
    Hypothesis HxGt : xGt = evalExpr (Slt (Var type XK xc) (Var type XK xp)).
    Hypothesis HxEq : xEq = Zmod.eqb xp xc.
    Hypothesis HpBig : pBig = (uZero uc || xGt) || (xEq && negb (Zmod.to_Z pext <? Zmod.to_Z cext)).
    Hypothesis Hcz : cz = if uZero uc then evalExpr (cst WF 0) else cext.
    Hypothesis HsBig : sBig = if pBig then sp else sc.
    Hypothesis HsSm : sSm = if pBig then sc else sp.
    Hypothesis HxBig : xBig = if pBig then xp else xc.
    Hypothesis HxSm : xSm = if pBig then xc else xp.
    Hypothesis Hbig : big = if pBig then pext else cz.
    Hypothesis Hsm : sm = if pBig then cz else pext.
    Hypothesis Hal : al = evalLetExpr (alignAdd e type WF sBig sSm xBig xSm big sm).
    Hypothesis Hr : r = al.(Fst).
    Hypothesis Hst : st = al.(Snd).(Fst).
    Hypothesis HxR : xR = evalExpr (Add [Var type XK xBig; cst (e + 3) 1]).
    Hypothesis HsR : sR = evalExpr (ITE (And [isZero (Var type (Bit WF) r); Not (Var type Bool st)])
                                        (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) (Var type Bool sBig)).

    Local Abbreviation Sa := (Zmod.to_Z (uSig ua)).
    Local Abbreviation Sb := (Zmod.to_Z (uSig ub)).
    Local Abbreviation Sc := (Zmod.to_Z (uSig uc)).
    Local Abbreviation Xa := (Zmod.signed (uExp ua)).
    Local Abbreviation Xb := (Zmod.signed (uExp ub)).
    Local Abbreviation Xc := (Zmod.signed (uExp uc)).

    Lemma pw_facts : 4 <= 2 ^ f /\ 2 ^ (f + 1) = 2 * 2 ^ f /\ 2 ^ (2 * f) = 2 ^ f * 2 ^ f /\
      2 ^ (2 * f + 1) = 2 * 2 ^ (2 * f) /\ 2 ^ (2 * f + 2) = 4 * 2 ^ (2 * f) /\
      2 ^ (2 * f + 3) = 8 * 2 ^ (2 * f) /\ 2 ^ (2 * f + 4) = 16 * 2 ^ (2 * f) /\
      2 ^ (2 * f + 5) = 32 * 2 ^ (2 * f) /\ 2 ^ WF = 64 * 2 ^ (2 * f) /\ 2 ^ (f + 4) = 16 * 2 ^ f /\
      2 ^ e = 2 * 2 ^ (e - 1) /\ 2 ^ (e + 2) = 8 * 2 ^ (e - 1) /\ 2 ^ (e + 3) = 16 * 2 ^ (e - 1).
    Proof.
      pose proof HeM.
      assert (P : forall k j, 0 <= k -> 0 <= j -> 2 ^ (k + j) = 2 ^ j * 2 ^ k) by (intros; rewrite Z.pow_add_r by lia; lia).
      split; [change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia |].
      rewrite (P f 1), (P (2 * f) 1), (P (2 * f) 2), (P (2 * f) 3), (P (2 * f) 4), (P (2 * f) 5), (P (2 * f) 6), (P f 4) by lia.
      replace (2 * f) with (f + f) by lia. rewrite (P f f) by lia.
      replace e with ((e - 1) + 1) at 1 by lia. replace (e + 2) with ((e - 1) + 3) by lia. replace (e + 3) with ((e - 1) + 4) by lia.
      rewrite !(P (e - 1)) by lia. cbn. lia.
    Qed.

    Lemma nrm_spec : evalLetExpr (normRound false e f type WF sR xR r st rm) =
      (ofB (BinarySingleNaN.Bfma (modeOf rm) A B C) ,,
       (finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B + BinarySingleNaN.B2R C)%R ,, tt)).
    Proof.
      pose proof HeM as He0.
      destruct pw_facts as (F4 & F1 & F2 & F21 & F22 & F23 & F24 & F25 & F26 & Ff4 & E1 & E2 & E3).
      assert (F2b : 2 ^ f <= 2 ^ (2 * f)) by (apply Z.pow_le_mono_r; lia).
      assert (Ffl : f < 2 ^ f) by (apply Z.pow_gt_lin_r; lia).
      assert (Eel : e < 2 ^ e) by (apply Z.pow_gt_lin_r; lia).
      assert (HWF : 0 < WF < 2 ^ (e + 2)) by lia.
      destruct HA as (HAn & HAi & HAz & HAs & HAv). destruct HB as (HBn & HBi & HBz & HBs & HBv).
      destruct HC as (HCn & HCi & HCz & HCs & HCv).
      assert (HAnan : BinarySingleNaN.is_nan A = false) by (destruct A; try discriminate; reflexivity).
      assert (HBnan : BinarySingleNaN.is_nan B = false) by (destruct B; try discriminate; reflexivity).
      assert (HCnan : BinarySingleNaN.is_nan C = false) by (destruct C; try discriminate; reflexivity).
      destruct (HAv HAf) as (HSa & HXa & HAr). destruct (HBv HBf) as (HSb & HXb & HBr).
      rewrite (HAs HAnan) in HAr. rewrite (HBs HBnan) in HBr. cbn [xorb] in HBr.
      unfold fpEmin, fpEmax, fpBias in HXa, HXb.
      pose proof (bits.unsigned_range (uSig uc) ltac:(lia)) as HSc0.
      (* the product *)
      set (P := Sa * Sb).
      assert (HP : Zmod.to_Z prod = P) by (rewrite Hprod; apply prod_val).
      assert (HPr : 2 ^ (2 * f) <= P < 2 ^ (2 * f + 2)).
      { unfold P; rewrite F22, F2; split; [apply Z.mul_le_mono_nonneg; lia |].
        replace (4 * (2 ^ f * 2 ^ f)) with ((2 * 2 ^ f) * (2 * 2 ^ f)) by ring. apply Z.mul_lt_mono_nonneg; lia. }
      assert (Htop' : top = (2 ^ (2 * f + 1) <=? P)).
      { rewrite Htop, bitSet_testbit by lia. rewrite HP. apply testbit_top; [lia |]. replace (2 * f + 1 + 1) with (2 * f + 2) by lia. lia. }
      clear Htop.
      assert (Hpn' : Zmod.to_Z pn = if top then P else 2 * P).
      { rewrite Hpn. destruct top; [exact HP |].
        symmetry in Htop'; apply Z.leb_gt in Htop'. cbn [evalExpr cst]. rewrite bits.unsigned_slu by lia.
        rewrite (tz_ofZ (2 * f + 2) 1) by lia. rewrite Z.shiftl_mul_pow2, HP by lia. rewrite Z.mod_small; lia. }
      assert (Hpnr : 2 ^ (2 * f + 1) <= Zmod.to_Z pn < 2 ^ (2 * f + 2)).
      { rewrite Hpn'. destruct top; symmetry in Htop'; [apply Z.leb_le in Htop' | apply Z.leb_gt in Htop']; lia. }
      assert (Hxp' : Zmod.signed xp = Xa + Xb + (if top then 1 else 0)).
      { transitivity (Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) (Xa + Xb + (if top then 1 else 0)))).
        - f_equal. rewrite Hxp. unfold expOff. cbn [evalExpr fold_left map cst].
          rewrite !Zmod.of_Z_add, !Zmod.of_Z_signed, Zmod.add_0_l. destruct top; reflexivity.
        - apply (signed_k e He0). destruct top; lia. }
      assert (Hpext' : Zmod.to_Z pext = 8 * Zmod.to_Z pn).
      { rewrite Hpext. cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr cst].
        rewrite (tz_ofZ WF 3) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
        match goal with |- context [Zmod.unsigned ?x * 8] => replace (Zmod.unsigned x) with (Zmod.to_Z pn) by reflexivity end.
        rewrite Z.mod_small; lia. }
      assert (Hcext' : Zmod.to_Z cext = Sc * 2 ^ (f + 4)).
      { rewrite Hcext. cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr cst].
        rewrite (tz_ofZ WF (f + 4)) by lia. rewrite Z.shiftl_mul_pow2, Hsigc by lia. rewrite Z.mod_small; [reflexivity |].
        split; [apply Z.mul_nonneg_nonneg; lia |]. rewrite Ff4, F26, F2.
        apply Z.lt_le_trans with ((2 * 2 ^ f) * (16 * 2 ^ f)); [apply Z.mul_lt_mono_pos_r; lia |].
        replace ((2 * 2 ^ f) * (16 * 2 ^ f)) with (32 * (2 ^ f * 2 ^ f)) by ring.
        assert (0 <= 2 ^ f * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia). lia. }
      assert (HxGt' : xGt = (Xc <? Zmod.signed xp)) by (rewrite HxGt, slt_eval by lia; cbn [evalExpr]; rewrite Hxc; reflexivity).
      assert (HxEq' : xEq = (Zmod.signed xp =? Xc)).
      { rewrite HxEq, Hxc. destruct (Zmod.eqb_spec xp (uExp uc)) as [-> | Hn]; [symmetry; apply Z.eqb_refl |].
        symmetry; apply Z.eqb_neq; intros H; apply Hn, Zmod.signed_inj; exact H. }
      assert (Hcz' : Zmod.to_Z cz = if uZero uc then 0 else Zmod.to_Z cext).
      { rewrite Hcz; destruct (uZero uc); [cbn [evalExpr cst]; apply tz_ofZ; lia | reflexivity]. }
      clear Hxp Hpext Hcext HxGt HxEq Hcz Hpn.
      (* the exact value *)
      set (K := 2 * f + 4).
      assert (HvAB : (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B)%R =
                     cond_Ropp sp (F2R (Float radix2 (Zmod.to_Z pext) (Zmod.signed xp - K)))).
      { rewrite HAr, HBr, Hsp.
        assert (HF : (F2R (Float radix2 Sa (Xa - f)) * F2R (Float radix2 Sb (Xb - f)))%R =
                     F2R (Float radix2 (Zmod.to_Z pext) (Zmod.signed xp - K))).
        { assert (HF0 : (F2R (Float radix2 Sa (Xa - f)) * F2R (Float radix2 Sb (Xb - f)))%R = F2R (Float radix2 P (Xa - f + (Xb - f)))).
          { unfold F2R, P; cbn [Fnum Fexp]. rewrite mult_IZR, bpow_plus. ring. }
          rewrite HF0, Hpext', Hpn', Hxp'. unfold K.
          destruct top.
          - rewrite <- (F2R_scale P 3 (Xa - f + (Xb - f))) by lia. f_equal; f_equal; [change (2 ^ 3) with 8; lia | lia].
          - rewrite <- (F2R_scale P 4 (Xa - f + (Xb - f))) by lia. f_equal; f_equal; [change (2 ^ 4) with 16; lia | lia]. }
        rewrite <- HF. destruct np, (uSign ua), (uSign ub); cbn [xorb cond_Ropp]; ring. }
      assert (HvC : BinarySingleNaN.B2R C = cond_Ropp sc (F2R (Float radix2 (Zmod.to_Z cz) (Xc - K)))).
      { rewrite Hcz'. destruct (uZero uc) eqn:HZ.
        - destruct C; try discriminate. unfold F2R; cbn [Fnum Fexp BinarySingleNaN.B2R]. rewrite Rmult_0_l. destruct sc; cbn; ring.
        - assert (HCs' : BinarySingleNaN.is_finite_strict C = true) by (destruct C; try discriminate; reflexivity).
          destruct (HCv HCs') as (_ & _ & HCr). rewrite HCr, (HCs HCnan), Hcext', <- Hsc. cbn [xorb].
          unfold K. rewrite <- (F2R_scale Sc (f + 4) (Xc - f)) by lia. f_equal; f_equal; f_equal; lia. }
      set (v := (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B + BinarySingleNaN.B2R C)%R).
      assert (HCnz : uZero uc = false -> 2 ^ f <= Sc < 2 ^ (f + 1) /\ fpEmin e - f <= Xc <= fpEmax e).
      { intros HZ. assert (HCs' : BinarySingleNaN.is_finite_strict C = true) by (rewrite HZ in HCz; destruct C; try discriminate; reflexivity).
        destruct (HCv HCs') as (H1 & H2 & _). split; assumption. }
      unfold fpEmin, fpEmax, fpBias in HCnz.
      (* the big and the small operand *)
      assert (G : 2 ^ (2 * f + 4) <= Zmod.to_Z big < 2 ^ (2 * f + 5) /\ 0 <= Zmod.to_Z sm < 2 ^ (2 * f + 5) /\
                  Zmod.to_Z sm mod 8 = 0 /\
                  (Zmod.to_Z sm <> 0 -> Zmod.signed xSm <= Zmod.signed xBig /\ Zmod.signed xBig - Zmod.signed xSm < 2 ^ (e + 2)) /\
                  (Zmod.to_Z sm <> 0 -> Zmod.signed xSm = Zmod.signed xBig -> Zmod.to_Z sm <= Zmod.to_Z big) /\
                  v = (cond_Ropp sBig (F2R (Float radix2 (Zmod.to_Z big) (Zmod.signed xBig - K))) +
                       cond_Ropp sSm (F2R (Float radix2 (Zmod.to_Z sm) (Zmod.signed xSm - K))))%R /\
                  - 2 ^ e - 2 * f <= Zmod.signed xBig <= 2 ^ e /\ Bool.eqb sBig sSm = Bool.eqb sp sc).
      { assert (Hm8 : (Sc * 2 ^ (f + 4)) mod 8 = 0).
        { replace (Sc * 2 ^ (f + 4)) with ((Sc * 2 ^ (f + 1)) * 8) by (replace (f + 4) with ((f + 1) + 3) by lia; rewrite (Z.pow_add_r 2 (f + 1) 3) by lia; change (2 ^ 3) with 8; ring).
          apply Z.mod_mul; lia. }
        rewrite HsBig, HsSm, HxBig, HxSm, Hbig, Hsm. unfold v. rewrite HvAB, HvC. rewrite Hxc.
        destruct pBig; rewrite Hcz'.
        - split; [rewrite Hpext'; lia |]. rewrite Hcext'. destruct (uZero uc) eqn:HZ.
          + split; [lia |]. split; [reflexivity |]. split; [lia |]. split; [lia |]. split; [reflexivity |].
            split; [destruct top; lia | reflexivity].
          + destruct (HCnz eq_refl) as (HSc & HXc).
            assert (L1 : 2 ^ (2 * f + 4) <= Sc * 2 ^ (f + 4)).
            { replace (2 ^ (2 * f + 4)) with (2 ^ f * 2 ^ (f + 4)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
              apply Z.mul_le_mono_nonneg_r; lia. }
            assert (L2 : Sc * 2 ^ (f + 4) < 2 ^ (2 * f + 5)).
            { replace (2 ^ (2 * f + 5)) with (2 ^ (f + 1) * 2 ^ (f + 4)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
              apply Z.mul_lt_mono_pos_r; lia. }
            set (T := Sc * 2 ^ (f + 4)) in *.
            split; [lia |]. split; [exact Hm8 |].
            cbn [orb] in HpBig. rewrite HxGt', HxEq', Hcext' in HpBig. fold T in HpBig.
            split; [intros _; assert (Xc <= Zmod.signed xp) by (revert HpBig; destruct (Z.ltb_spec Xc (Zmod.signed xp)), (Z.eqb_spec (Zmod.signed xp) Xc); cbn; intros HpBig; try discriminate HpBig; lia); destruct top; lia |].
            split.
            * intros _ Heq. replace (Xc <? Zmod.signed xp) with false in HpBig by (symmetry; apply Z.ltb_ge; lia).
              replace (Zmod.signed xp =? Xc) with true in HpBig by (symmetry; apply Z.eqb_eq; lia).
              revert HpBig; destruct (Z.ltb_spec (Zmod.to_Z pext) T); cbn [negb]; intros HpBig; [discriminate HpBig | lia].
            * split; [reflexivity |]. split; [destruct top; lia | reflexivity].
        - cbn [orb] in HpBig. destruct (uZero uc) eqn:HZ; [discriminate HpBig |]. cbn [orb] in HpBig.
          destruct (HCnz eq_refl) as (HSc & HXc). rewrite HxGt', HxEq', Hcext' in HpBig.
          assert (L1 : 2 ^ (2 * f + 4) <= Sc * 2 ^ (f + 4)).
          { replace (2 ^ (2 * f + 4)) with (2 ^ f * 2 ^ (f + 4)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
            apply Z.mul_le_mono_nonneg_r; lia. }
          assert (L2 : Sc * 2 ^ (f + 4) < 2 ^ (2 * f + 5)).
          { replace (2 ^ (2 * f + 5)) with (2 ^ (f + 1) * 2 ^ (f + 4)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
            apply Z.mul_lt_mono_pos_r; lia. }
          rewrite Hcext'. set (T := Sc * 2 ^ (f + 4)) in *. split; [lia |]. split; [rewrite Hpext'; lia |]. split; [rewrite Hpext', Z.mul_comm; apply Z.mod_mul; lia |].
          assert (HxL : Zmod.signed xp <= Xc) by (revert HpBig; destruct (Z.ltb_spec Xc (Zmod.signed xp)); cbn; intros HpBig; [discriminate HpBig | lia]).
          replace (Xc <? Zmod.signed xp) with false in HpBig by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in HpBig.
          split; [intros _; split; [exact HxL | destruct top; lia] |]. split.
          + intros _ Heq. replace (Zmod.signed xp =? Xc) with true in HpBig by (symmetry; apply Z.eqb_eq; lia).
            revert HpBig; destruct (Z.ltb_spec (Zmod.to_Z pext) T); cbn [negb]; intros HpBig; [lia | discriminate HpBig].
          + split; [apply Rplus_comm |]. split; [lia |]. destruct sp, sc; reflexivity. }
      destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
      destruct (alignAdd_eval WF sBig sSm xBig xSm big sm HWF) as (sh & Hsh & Hshm & Hst' & Hadd & Hsub).
      rewrite <- Hal, <- Hr in Hadd, Hsub. rewrite <- Hal, <- Hst in Hst'.
      assert (G4' : Zmod.to_Z sm <> 0 -> Zmod.signed xSm <= Zmod.signed xBig /\ sh = Z.min (Zmod.signed xBig - Zmod.signed xSm) WF).
      { intros Hz. destruct (G4 Hz). split; [lia | apply Hshm; lia]. }
      pose proof (align_math f Hf sBig sSm (Zmod.signed xBig) (Zmod.signed xSm) (Zmod.to_Z big) (Zmod.to_Z sm) sh G1 G2 G3 Hsh G4' G5) as AM.
      cbv zeta in AM. fold K in AM. rewrite <- Hst', <- G6 in AM.
      destruct AM as (Hr0 & Hr1 & Hr2 & (l & Hin & Hl) & Hvs).
      assert (HR : Zmod.to_Z r = if Bool.eqb sBig sSm then Zmod.to_Z big + Zmod.to_Z sm / 2 ^ sh
                                 else Zmod.to_Z big - Zmod.to_Z sm / 2 ^ sh - b2z st).
      { destruct (Bool.eqb sBig sSm) eqn:Hq.
        - apply Hadd; [reflexivity | lia].
        - rewrite Hst'. apply Hsub; [reflexivity | rewrite <- Hst'; lia]. }
      rewrite <- HR in Hr0, Hr1, Hr2, Hin. clear Hadd Hsub HR.
      set (R := Zmod.to_Z r) in *.
      clear HpBig HxGt' HxEq' Hcz' Hpext' Hcext' Hpn' Htop' G1 G2 G3 G4 G4' G5 G6 Hsh Hshm Hst' Hal
        HvAB HvC HAr HBr HAv HBv HCv HCnz HSa HSb HXa HXb HP HPr Hpnr Hxp' HSc0 HAn HAi HAz HBn HBi HBz HCn HCi HCz
        Hprod Hsigc HsBig HsSm HxBig HxSm Hbig Hsm Hxc.
      assert (HxR' : Zmod.signed xR = Zmod.signed xBig + 1).
      { rewrite HxR. cbn [evalExpr fold_left map cst]. rewrite Zmod.add_0_l.
        rewrite <- (Zmod.of_Z_signed xBig) at 1. rewrite <- Zmod.of_Z_add. apply (signed_k e He0). clear -G7 E1 Hpe Hf He0. lia. }
      assert (HsR' : sR = if (R =? 0) && negb st then (Zmod.to_Z rm =? 2) else sBig).
      { rewrite HsR.
        change (evalExpr (ITE (And [isZero (Var type (Bit WF) r); Not (Var type Bool st)]) (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) (Var type Bool sBig)))
          with (if evalExpr (isZero (Var type (Bit WF) r)) && negb st then evalExpr (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) else sBig).
        rewrite (isZero_eval WF r), eqRdn. reflexivity. }
      assert (HAfin : BinarySingleNaN.is_finite A = true) by (destruct A; try discriminate; reflexivity).
      assert (HBfin : BinarySingleNaN.is_finite B = true) by (destruct B; try discriminate; reflexivity).
      pose proof (@BinarySingleNaN.Bfma_correct (f + 1) (2 ^ (e - 1)) _ _ (modeOf rm) A B C HAfin HBfin HCf) as HBF.
      cbv zeta in HBF. fold v in HBF.
      clear HsR HxR.
      destruct (Z.eqb_spec R 0) as [HR0 | HRn].
      - (* exact cancellation: a zero with the sign of the rounding mode *)
        assert (Hst0 : st = false) by (destruct st; [specialize (Hr1 eq_refl); lia | reflexivity]).
        assert (HsR0 : sR = (Zmod.to_Z rm =? 2)).
        { rewrite HsR', Hst0. replace (R =? 0) with true by (symmetry; apply Z.eqb_eq; exact HR0). reflexivity. }
        rewrite (normRound_zero WF sR xR r st rm HR0 Hst0).
        assert (Hv0 : v = 0%R).
        { assert (Hl0 : l = loc_Exact) by (apply Hl; exact Hst0). rewrite Hl0, HR0 in Hin.
          inversion Hin as [Hx |]. rewrite F2R_0 in Hx.
          destruct (Req_dec v 0) as [H0 | H0]; [exact H0 | pose proof (Rabs_pos_lt v H0); lra]. }
        rewrite Hv0 in HBF. rewrite (round_0 radix2 (SpecFloat.fexp (f + 1) (2 ^ (e - 1))) (round_mode (modeOf rm))) in HBF.
        rewrite Rabs_R0, Rlt_bool_true in HBF by apply bpow_gt_0.
        destruct HBF as (H1 & H2 & H3). rewrite Rcompare_Eq in H3 by reflexivity.
        assert (Hne : Bool.eqb sp sc = false).
        { rewrite <- G8. destruct (Bool.eqb sBig sSm); [specialize (Hr2 eq_refl); lia | reflexivity]. }
        rewrite Hsp, Hsc in Hne.
        unfold BinarySingleNaN.Bfma_szero in H3. rewrite (HAs HAnan), (HBs HBnan), (HCs HCnan) in H3.
        replace (Bool.eqb (xorb (xorb np (uSign ua)) (xorb false (uSign ub))) (xorb false (uSign uc))) with false in H3
          by (rewrite <- Hne; destruct np, (uSign ua), (uSign ub), (uSign uc); reflexivity).
        rewrite modeDN in H3.
        assert (HBz : BinarySingleNaN.Bfma (modeOf rm) A B C = BinarySingleNaN.B754_zero (Zmod.to_Z rm =? 2))
          by (apply BinarySingleNaN.B2R_Bsign_inj; [exact H2 | reflexivity | rewrite H1; reflexivity | rewrite H3; reflexivity]).
        rewrite HBz, ofB_zero, Hv0, flags0, noFlags_eq, HsR0. reflexivity.
      - (* a non-zero sum: normalize and round *)
        assert (HRp : 0 < R) by lia.
        assert (HsR1 : sR = sBig) by (rewrite HsR'; replace (R =? 0) with false by (symmetry; apply Z.eqb_neq; exact HRn); reflexivity).
        set (k := WF - 1 - Z.log2 R). set (d := WF - (f + 3)).
        pose proof (norm_window f Hf WF R ltac:(lia) ltac:(lia)) as NW. cbv zeta in NW. fold k d in NW.
        destruct NW as (Hk & HN & HSr).
        assert (HxRb : - 2 ^ (e + 2) <= Zmod.signed xR - WF) by lia.
        pose proof (normRound_eval e f He0 Hf WF sR xR r st rm ltac:(lia) ltac:(lia) HRp HxRb) as HN'.
        cbv zeta in HN'. fold R in HN'. fold k d in HN'. rewrite HN'.
        set (st2 := st || negb ((R * 2 ^ k) mod 2 ^ d =? 0)).
        pose proof (roundPack_Z e f He0 Hf Hpe sR (Zmod.of_Z (2 ^ (e + 3)) (Zmod.signed xR - k)) (Zmod.of_Z (2 ^ (f + 3)) (R * 2 ^ k / 2 ^ d)) st2 rm) as RP.
        cbv zeta in RP. rewrite RP.
        assert (HX : Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) (Zmod.signed xR - k)) = Zmod.signed xR - k) by (apply (signed_k e He0); lia).
        assert (HS : Zmod.to_Z (Zmod.of_Z (2 ^ (f + 3)) (R * 2 ^ k / 2 ^ d)) = R * 2 ^ k / 2 ^ d) by (apply tz_ofZ; lia).
        rewrite HX, HS, HsR1.
        set (X := Zmod.signed xR - k). set (S := R * 2 ^ k / 2 ^ d).
        assert (Hin' : inbetween_float radix2 R (Zmod.signed xR - (WF - 1)) (Rabs v) l)
          by (replace (Zmod.signed xR - (WF - 1)) with (Zmod.signed xBig - K) by (unfold K; lia); exact Hin).
        assert (Hkd : st = true -> k <= d).
        { intros Hs. specialize (Hr1 Hs).
          assert (2 * f + 3 <= Z.log2 R) by (rewrite <- (Z.log2_pow2 (2 * f + 3)) by lia; apply Z.log2_le_mono; lia).
          unfold k, d; lia. }
        pose proof (norm_loc f Hf WF R (Zmod.signed xR) st v l ltac:(lia) ltac:(lia) Hin' Hl) as NL.
        cbv zeta in NL. fold k d in NL. destruct (NL Hkd) as (l2 & Hin2 & Hl2). fold st2 in Hl2.
        assert (Hpos : (0 < Rabs v)%R).
        { pose proof (inbetween_float_bounds radix2 _ _ _ _ Hin) as [Hlo _]. eapply Rlt_le_trans; [| exact Hlo].
          apply F2R_gt_0; cbn; lia. }
        assert (Hs : Rlt_bool v 0 = sBig).
        { rewrite Hvs. destruct sBig; cbn [cond_Ropp]; [apply Rlt_bool_true; lra | apply Rlt_bool_false; lra]. }
        assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)); change (2 ^ 3) with 8 in *; lia).
        assert (Hbf : toB (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) sBig X S st2)) = BinarySingleNaN.Bfma (modeOf rm) A B C).
        { apply (rp_result e f Hf Hpe (Zmod.to_Z rm) sBig X S st2 v l2 Hrm HSr Hin2 Hl2 Hs).
          change (modeZ (Zmod.to_Z rm)) with (modeOf rm). refine (if_impl _ _ _ _ _ _ _ HBF).
          - intros (H1 & H2 & H3). split; [exact H1 |]. split; [exact H2 |]. rewrite H3, <- Hs.
            destruct (Rcompare_spec v 0) as [Hlt | Heq | Hgt].
            + rewrite Rlt_bool_true by exact Hlt; reflexivity.
            + exfalso. rewrite Heq, Rabs_R0 in Hpos. lra.
            + rewrite Rlt_bool_false by lra; reflexivity.
          - intros HBF'. rewrite HBF', Hs. reflexivity. }
        assert (Hnn : BinarySingleNaN.is_nan (BinarySingleNaN.Bfma (modeOf rm) A B C) = false).
        { refine (if_elim _ _ _ _ _ _ HBF).
          - intros (_ & H2 & _). destruct (BinarySingleNaN.Bfma (modeOf rm) A B C); try discriminate; reflexivity.
          - intros HBF'. rewrite (is_nan_B2SF e f), HBF'. unfold BinarySingleNaN.binary_overflow. destruct (BinarySingleNaN.overflow_to_inf (modeOf rm) (Rlt_bool v 0)); reflexivity. }
        rewrite <- Hbf. rewrite ofB_toB by (rewrite Hbf; exact Hnn).
        f_equal. f_equal. unfold finiteFlags. change (modeOf rm) with (modeZ (Zmod.to_Z rm)).
        rewrite (rp_flags e f Hf Hpe (Zmod.to_Z rm) sBig X S st2 v l2 Hrm HSr Hin2 Hl2 Hs). reflexivity.
    Qed.
  End Nrm.


  (* ---------------------------------------------------------------------------
   * The special cases and the dispatch of `fmaFinish`
   * --------------------------------------------------------------------------- *)

  Lemma fma_ret : forall (c : bits W) (uc : type (FpUnpK e f)) (sp anyNaN invP pInf pZero infCan nvN zSign : bool)
      (nrm : type (FpOutK e f)),
    evalLetExpr (@RetE type (FpOutK e f)
      (ITE (Or [ (Var type Bool anyNaN) ; (Var type Bool invP) ])
           (mkOut e f type (qnanE e f type) (mkFlags type ((Var type Bool nvN)) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
      (ITE ((Var type Bool infCan)) (mkOut e f type (qnanE e f type) (mkFlags type (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)))
      (ITE ((Var type Bool pInf)) (mkOut e f type (infE e f type ((Var type Bool sp))) (noFlags type))
      (ITE (ReadStruct (Var type (FpUnpK e f) uc) (@Build_FinType 7 2 I)) (mkOut e f type (Var type (FpBits e f) c) (noFlags type))
      (ITE (And [ (Var type Bool pZero) ; ReadStruct (Var type (FpUnpK e f) uc) (@Build_FinType 7 1 I) ]) (mkOut e f type (zeroE e f type ((Var type Bool zSign))) (noFlags type))
      (ITE ((Var type Bool pZero)) (mkOut e f type (Var type (FpBits e f) c) (noFlags type))
      (Var type (FpOutK e f) nrm)))))))) =
    if anyNaN || invP then (evalExpr (qnanE e f type) ,, (mkFl nvN false false false false ,, tt))
    else if infCan then (evalExpr (qnanE e f type) ,, (mkFl true false false false false ,, tt))
    else if pInf then (evalExpr (infE e f type (Var type Bool sp)) ,, (mkFl false false false false false ,, tt))
    else if uInf uc then (c ,, (mkFl false false false false false ,, tt))
    else if pZero && uZero uc then (evalExpr (zeroE e f type (Var type Bool zSign)) ,, (mkFl false false false false false ,, tt))
    else if pZero then (c ,, (mkFl false false false false false ,, tt))
    else nrm.
  Proof.
    intros c [us [uz [ui [un [usn [ux [ug []]]]]]]] sp anyNaN invP pInf pZero infCan nvN zSign nrm.
    destruct anyNaN; [destruct nvN; reflexivity |]. destruct invP; [destruct nvN; reflexivity |].
    destruct infCan; [reflexivity |]. destruct pInf; [reflexivity |]. destruct ui; [reflexivity |].
    destruct pZero, uz; reflexivity.
  Qed.

  Lemma flags_repr : forall m (x : bfloat), BinarySingleNaN.is_finite x = true ->
    finiteFlags (f + 1) (2 ^ (e - 1)) m (BinarySingleNaN.B2R x) = mkFl false false false false false.
  Proof.
    intros m x Hx. unfold finiteFlags, roundFlags; cbv zeta.
    rewrite (round_generic radix2 (SpecFloat.fexp (f + 1) (2 ^ (e - 1))) (round_mode m) _ (BinarySingleNaN.generic_format_B2R _ _ x)).
    rewrite Rlt_bool_true by (apply BinarySingleNaN.abs_B2R_lt_emax).
    rewrite Req_bool_true by reflexivity. cbn [negb orb]. rewrite andb_false_r. reflexivity.
  Qed.

  Lemma xorb_np : forall np a b, xorb (xorb (xorb np a) b) np = xorb a b.
  Proof. intros [|] [|] [|]; reflexivity. Qed.

  Lemma flags_pz : forall m (A B C : bfloat), (isZeroF A || isZeroF B) = true -> BinarySingleNaN.is_finite C = true ->
    finiteFlags (f + 1) (2 ^ (e - 1)) m (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B + BinarySingleNaN.B2R C)%R =
    mkFl false false false false false.
  Proof.
    intros m A B C HZ HC. replace (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B + BinarySingleNaN.B2R C)%R with (BinarySingleNaN.B2R C).
    - apply flags_repr; exact HC.
    - destruct A, B; try discriminate HZ; cbn [BinarySingleNaN.B2R]; ring.
  Qed.

  Local Ltac fin_case Enrm HcC :=
    unfold fmaFlagsF; cbn [BinarySingleNaN.is_nan isInfF isZeroF BinarySingleNaN.is_finite BinarySingleNaN.is_finite_strict
      BinarySingleNaN.Bsign orb andb negb xorb]; rewrite ?xorb_np;
    first
      [ rewrite Enrm by reflexivity; reflexivity
      | cbn [BinarySingleNaN.Bfma BinarySingleNaN.Bsign]; try unfold BinarySingleNaN.Bfma_szero; cbn [BinarySingleNaN.Bsign];
        rewrite ?modeDN, ?flags_pz by reflexivity;
        first
          [ rewrite (HcC eq_refl); reflexivity
          | rewrite ?ofB_nan, ?ofB_zero, ?ofB_inf;
            first
              [ reflexivity
              | match goal with |- context [mkFl (?a || ?b || ?c || _) _ _ _ _] => destruct a, b, c; reflexivity end
              | match goal with |- context [Bool.eqb ?x ?y] =>
                  destruct (Bool.eqb x y) eqn:Heqb; cbn [negb];
                  [apply Bool.eqb_prop in Heqb; subst; rewrite ?ofB_inf; reflexivity | rewrite ?ofB_nan; reflexivity] end ] ] ].

  Lemma fmaFinish_spec : forall rm (c2 : bits W) ua ub uc np A B C,
    urel np ua A -> urel false ub B -> urel false uc C ->
    (BinarySingleNaN.is_nan C = false -> ofB C = c2) ->
    evalLetExpr (fmaFinish false e f type rm c2 ua ub uc np (evalExpr (sigProduct f type (uSig ua) (uSig ub)))) =
    (ofB (BinarySingleNaN.Bfma (modeOf rm) A B C) ,, (fmaFlagsF rm (uSNaN ua) (uSNaN ub) (uSNaN uc) A B C ,, tt)).
  Proof.
    intros rm c2 ua ub uc np A B C HA HB HC HcC.
    unfold fmaFinish.
    peel sp. peel sc. peel xc. peel top. peel pn. peel xp. peel pext. peel sigc. peel cext. peel xGt. peel xEq.
    peel pBig. peel cz. peel sBig. peel sSm. peel xBig. peel xSm. peel big. peel sm. peel al. peel r. peel st.
    peel xR. peel sR. peel nrm. peel anyNaN. peel invP. peel pInf. peel pZero. peel infCan. peel nvN. peel zSign.
    assert (Enrm : BinarySingleNaN.is_finite_strict A = true -> BinarySingleNaN.is_finite_strict B = true ->
                   BinarySingleNaN.is_finite C = true ->
                   nrm = (ofB (BinarySingleNaN.Bfma (modeOf rm) A B C) ,,
                          (finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
                             (BinarySingleNaN.B2R A * BinarySingleNaN.B2R B + BinarySingleNaN.B2R C)%R ,, tt))).
    { intros HAf HBf HCf. unfold nrm.
      exact (nrm_spec rm ua ub uc np A B C HA HB HC HAf HBf HCf (evalExpr (sigProduct f type (uSig ua) (uSig ub))) pn
               sp sc top xGt xEq pBig sBig sSm st sR xc xp xBig xSm xR pext cext cz big sm r sigc al
               eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
               eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl). }
    assert (Esp : sp = xorb (xorb (uSign ua) (uSign ub)) np) by reflexivity.
    assert (Esc : sc = uSign uc) by reflexivity.
    assert (EanyNaN : anyNaN = (uNaN ua || uNaN ub) || uNaN uc) by reflexivity.
    assert (EinvP : invP = (uInf ua && uZero ub) || (uZero ua && uInf ub)) by reflexivity.
    assert (EpInf : pInf = uInf ua || uInf ub) by reflexivity.
    assert (EpZero : pZero = uZero ua || uZero ub) by reflexivity.
    assert (EinfCan : infCan = (pInf && uInf uc) && negb (Bool.eqb sp sc)) by reflexivity.
    assert (EnvN : nvN = ((uSNaN ua || uSNaN ub) || uSNaN uc) || invP) by reflexivity.
    assert (EzSign : zSign = if Bool.eqb sp sc then sp else evalExpr (Eq (Var type (Bit 3) rm) (cst 3 RmRdn))) by reflexivity.
    rewrite eqRdn in EzSign.
    clearbody sp sc xc top pn xp pext sigc cext xGt xEq pBig cz sBig sSm xBig xSm big sm al r st xR sR nrm
      anyNaN invP pInf pZero infCan nvN zSign.
    rewrite fma_ret.
    rewrite EinfCan, EnvN, EzSign, EanyNaN, EinvP, EpInf, EpZero, Esp, Esc.
    clear EinfCan EnvN EzSign EanyNaN EinvP EpInf EpZero Esp Esc.
    destruct HA as (HAn & HAi & HAz & HAs & _). destruct HB as (HBn & HBi & HBz & HBs & _).
    destruct HC as (HCn & HCi & HCz & HCs & _).
    rewrite HAn, HAi, HAz, HBn, HBi, HBz, HCn, HCi, HCz.
    assert (HsA : BinarySingleNaN.is_nan A = false -> uSign ua = xorb np (BinarySingleNaN.Bsign A))
      by (intros Hn; rewrite (HAs Hn); destruct np, (uSign ua); reflexivity).
    assert (HsB : BinarySingleNaN.is_nan B = false -> uSign ub = xorb false (BinarySingleNaN.Bsign B))
      by (intros Hn; rewrite (HBs Hn); destruct (uSign ub); reflexivity).
    assert (HsC : BinarySingleNaN.is_nan C = false -> uSign uc = xorb false (BinarySingleNaN.Bsign C))
      by (intros Hn; rewrite (HCs Hn); destruct (uSign uc); reflexivity).
    clear HAn HAi HAz HBn HBi HBz HCn HCi HCz HAs HBs HCs.
    destruct A; try rewrite (HsA eq_refl).
    - destruct B; try rewrite (HsB eq_refl); destruct C; try rewrite (HsC eq_refl); fin_case Enrm HcC.
    - destruct B; try rewrite (HsB eq_refl); destruct C; try rewrite (HsC eq_refl); fin_case Enrm HcC.
    - destruct B; try rewrite (HsB eq_refl); destruct C; try rewrite (HsC eq_refl); fin_case Enrm HcC.
    - destruct B; try rewrite (HsB eq_refl); destruct C; try rewrite (HsC eq_refl); fin_case Enrm HcC.
  Qed.

  (* ---------------------------------------------------------------------------
   * The theorem
   * --------------------------------------------------------------------------- *)

  Theorem ffma_flocq_thm : ffma_flocq.
  Proof.
    intros np na rm a b c.
    pose proof (ffma_core np na rm a b c) as H; cbv zeta in H; destruct H as [Hres Hfl]. rewrite Hres, Hfl. clear Hres Hfl.
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    destruct (split_fields e f Hf Hpe c) as (sc & Ec & Mc & HMc & HEc & Hc).
    pose proof (flipC_bits na c sc Ec Mc HMc HEc Hc) as Hc2.
    pose proof (urel_sgn np _ _ (urel_fields a sa Ea Ma HMa HEa Ha)) as UA.
    pose proof (urel_fields b sb Eb Mb HMb HEb Hb) as UB.
    pose proof (urel_fields (flipC na c) (xorb na sc) Ec Mc HMc HEc Hc2) as UC.
    rewrite flipC_toB in UC.
    assert (HcC : BinarySingleNaN.is_nan (sgnF na (toB c)) = false -> ofB (sgnF na (toB c)) = flipC na c).
    { intros Hn. rewrite <- flipC_toB. apply ofB_toB. rewrite flipC_toB. exact Hn. }
    rewrite (fmaFinish_spec rm (flipC na c) _ _ _ np _ _ _ UA UB UC HcC).
    cbn [Fst Snd]. split; [reflexivity |].
    unfold fmaFlags. rewrite (isSNaN_u a sa Ea Ma HMa HEa Ha), (isSNaN_u b sb Eb Mb HMb HEb Hb), (isSNaN_u c sc Ec Mc HMc HEc Hc).
    rewrite (u_snan e f HeM Hf c sc Ec Mc HMc HEc Hc), (u_snan e f HeM Hf (flipC na c) (xorb na sc) Ec Mc HMc HEc Hc2).
    reflexivity.
  Qed.

End Fma.
