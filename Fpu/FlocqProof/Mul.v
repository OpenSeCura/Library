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
 * FMUL against Flocq's `Bmult` (`Mul.v`).
 *
 * `fmulRef rm a b` is the reference core (`FpCoreRef.fpuComputeRef`) on a decoded FMUL.
 * `fmul_flocq`: its result is Flocq's `Bmult` (in `BinarySingleNaN`, NaN encoded as the RISC-V
 * canonical NaN) and its flags are the IEEE flags of rounding the exact product (`Flags.v`), with
 * NV for a signaling NaN operand or `inf * 0`.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Section Mul.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation toBp := (toBp e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).

  (* Flocq's side conditions, as the instances its operations expect. *)
  Local Instance precGt : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  (* The decoded FMUL (`FpCore.FpOpDK`): only the `mul` family flag is set. *)
  Definition opMul : type FpOpDK :=
    (false ,, (true ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (false ,, (false ,, (false ,, tt)))))))))))))))))))))).

  Definition reqOf (op : type FpOpDK) (rm : bits 3) (a b c : bits W) (x : bits xlen) : type (FpReqK e f xlen) :=
    (op ,, (rm ,, (a ,, (b ,, (c ,, (x ,, tt)))))).

  (* FMUL in the reference core. *)
  Definition fmulRef (rm : bits 3) (a b : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqOf opMul rm a b Zmod.zero Zmod.zero)).

  (* Signaling NaN: a NaN whose quiet bit (the top fraction bit) is clear. *)
  Definition isSNaN (x : bits W) : bool :=
    match toBp x with
    | Binary.B754_nan _ _ _ pl _ => negb (Z.testbit (Zpos pl) (f - 1))
    | _ => false
    end.

  (* IEEE flags of FMUL. *)
  Definition mulFlags (rm : bits 3) (a b : bits W) : bits 5 :=
    match toB a, toB b with
    | BinarySingleNaN.B754_nan, _ | _, BinarySingleNaN.B754_nan =>
        mkFl (isSNaN a || isSNaN b) false false false false
    | BinarySingleNaN.B754_infinity _, BinarySingleNaN.B754_zero _
    | BinarySingleNaN.B754_zero _, BinarySingleNaN.B754_infinity _ => mkFl true false false false false
    | BinarySingleNaN.B754_finite _ _ _ _, BinarySingleNaN.B754_finite _ _ _ _ =>
        finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
          (Rmult (BinarySingleNaN.B2R (toB a)) (BinarySingleNaN.B2R (toB b)))
    | _, _ => mkFl false false false false false
    end.

  Definition fmul_flocq : Prop :=
    forall rm a b,
      (fmulRef rm a b) @% "res" = ofB (BinarySingleNaN.Bmult (modeOf rm) (toB a) (toB b)) /\
      (fmulRef rm a b) @% "flags" = mulFlags rm a b.

  (* ---------------------------------------------------------------------------
   * The FMUL path of the core
   * --------------------------------------------------------------------------- *)

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  Definition mulCore (rm : bits 3) (a b : bits W) : type (FpOutK e f) :=
    let ua := unp a in
    let ub := unp (evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) b)) in
    let prod := evalExpr (sigProduct f type (uSig ua) (uSig ub)) in
    evalLetExpr (mulFinish false e f type rm ua ub prod).

  Lemma fmul_core_res : forall rm a b, (fmulRef rm a b) @% "res" = (mulCore rm a b).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma fmul_core_flags : forall rm a b, (fmulRef rm a b) @% "flags" = (mulCore rm a b).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma HeM : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Lemma flip0 : forall b : bits W, evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) b) = b.
  Proof.
    intros b; pose proof HeM; cbn [evalExpr flipSign fold_left map evalXorBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault andb cst].
    change (Zmod.xor (Zmod.xor Zmod.zero b) (Zmod.of_Z (2 ^ W) 0) = b). apply Zmod.unsigned_inj. rewrite !bits.unsigned_xor, Zmod.unsigned_0, Z.lxor_0_l, Zmod.unsigned_of_Z, Z.mod_0_l, Z.lxor_0_r
      by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.

  (* `mulFinish false`, transcribed. *)
  Definition mulV (rm : bits 3) (ua ub : type (FpUnpK e f)) (prod : bits (2 * f + 2)) : type (FpOutK e f) :=
    let s := xorb (uSign ua) (uSign ub) in
    let xP := evalExpr (Add [Var type (Bit (e + 3)) (uExp ua); Var type (Bit (e + 3)) (uExp ub); cst (e + 3) (1 - expOff false e)]) in
    let invP := (uInf ua && uZero ub) || (uZero ua && uInf ub) in
    let nv := uSNaN ua || uSNaN ub || invP in
    if (uNaN ua || uNaN ub) || invP
    then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if uInf ua || uInf ub then (evalExpr (infE e f type (ConstBool s)) ,, (Zmod.of_Z _ 0 ,, tt))
    else if uZero ua || uZero ub then (evalExpr (zeroE e f type (ConstBool s)) ,, (Zmod.of_Z _ 0 ,, tt))
    else evalLetExpr (normRound false e f type (2 * f + 2) s xP prod false rm).

  Lemma mulFinish_V : forall rm ua ub prod, evalLetExpr (mulFinish false e f type rm ua ub prod) = mulV rm ua ub prod.
  Proof. intros; exact eq_refl. Qed.

  (* ---------------------------------------------------------------------------
   * Classes of the operands
   * --------------------------------------------------------------------------- *)

  Local Abbreviation eminF := (SpecFloat.emin (f + 1) (2 ^ (e - 1))).

  Definition clsP (x : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) (s : bool) (E M : Z) : Prop :=
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

  Lemma ofB_inf : forall s, ofB (BinarySingleNaN.B754_infinity s) = evalExpr (infE e f type (ConstBool s)).
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

  Lemma ofB_zero : forall s, ofB (BinarySingleNaN.B754_zero s) = evalExpr (zeroE e f type (ConstBool s)).
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

  (* ---------------------------------------------------------------------------
   * Finite non-zero operands
   * --------------------------------------------------------------------------- *)

  Section Fin.
    Variable x : bits W.
    Variables (s : bool) (E M : Z).
    Hypothesis HM : 0 <= M < 2 ^ f.
    Hypothesis HE : 0 <= E < 2 ^ e.
    Hypothesis Hx : Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M.
    Hypothesis Hn : E <> 2 ^ e - 1.
    Hypothesis Hz : E <> 0 \/ M <> 0.

    Lemma fin_facts :
      let Xx := Zmod.signed (uExp (unp x)) in
      let Sg := Zmod.to_Z (uSig (unp x)) in
      2 ^ f <= Sg < 2 ^ (f + 1) /\ fpEmin e - f <= Xx <= fpEmax e /\
      BinarySingleNaN.B2R (toB x) = cond_Ropp s (F2R (Float radix2 Sg (Xx - f))) /\
      BinarySingleNaN.is_finite (toB x) = true /\ BinarySingleNaN.Bsign (toB x) = s.
    Proof.
      intros Xx Sg.
      pose proof (u_value e f HeM Hf Hpe x s E M HM HE Hx Hn Hz) as HV; cbv zeta in HV; fold Xx Sg in HV.
      destruct HV as (HS & HX & HV).
      pose proof (cls x s E M HM HE Hx) as C.
      destruct (toB x) as [s' | s' | | s' m ex Hb]; cbn [clsP] in C.
      - lia.
      - lia.
      - lia.
      - destruct C as (-> & _ & _ & Hm & Hex).
        refine (conj HS (conj HX (conj _ (conj eq_refl eq_refl)))).
        change (BinarySingleNaN.B2R (BinarySingleNaN.B754_finite s m ex Hb)) with (F2R (Float radix2 (cond_Zopp s (Zpos m)) ex)).
        rewrite F2R_cond_Zopp, HV, Hm, Hex; reflexivity.
    Qed.
  End Fin.

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

  Lemma xP_val : forall ea eb : bits (e + 3),
    - 2 ^ (e - 1) - f <= Zmod.signed ea <= 2 ^ (e - 1) -> - 2 ^ (e - 1) - f <= Zmod.signed eb <= 2 ^ (e - 1) ->
    Zmod.signed (evalExpr (Add [Var type (Bit (e + 3)) ea; Var type (Bit (e + 3)) eb; cst (e + 3) (1 - expOff false e)])) =
    Zmod.signed ea + Zmod.signed eb + 1.
  Proof.
    intros ea eb Ha Hb. pose proof HeM.
    cbn [evalExpr fold_left map cst]. unfold expOff.
    rewrite <- (Zmod.of_Z_signed ea), <- (Zmod.of_Z_signed eb) at 1.
    rewrite <- (Zmod.of_Z_0 (2 ^ (e + 3))), <- !Zmod.of_Z_add.
    apply signed_of_Z_small; [lia |].
    replace (e + 3 - 1) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; change (2 ^ 3) with 8; lia.
  Qed.

  Lemma Rlt_bool_cond_Ropp : forall s p, (0 < p)%R -> Rlt_bool (cond_Ropp s p) 0 = s.
  Proof.
    intros [|] p Hp; cbn [cond_Ropp].
    - apply Rlt_bool_true; lra.
    - apply Rlt_bool_false; lra.
  Qed.

  Lemma is_nan_of_correct : forall (b : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) m s,
    BinarySingleNaN.is_finite b = true \/ BinarySingleNaN.B2SF b = BinarySingleNaN.binary_overflow (f + 1) (2 ^ (e - 1)) m s ->
    BinarySingleNaN.is_nan b = false.
  Proof.
    intros b m s [H | H]; [destruct b; try reflexivity; discriminate H |].
    rewrite is_nan_B2SF, H. unfold BinarySingleNaN.binary_overflow; destruct (overflow_to_inf m s); reflexivity.
  Qed.

  (* Both operands finite and non-zero: the product goes through `normRound`. *)
  Lemma mul_finite : forall rm a b sa Ea Ma sb Eb Mb,
    0 <= Ma < 2 ^ f -> 0 <= Ea < 2 ^ e -> Zmod.to_Z a = b2z sa * 2 ^ (f + e) + Ea * 2 ^ f + Ma ->
    0 <= Mb < 2 ^ f -> 0 <= Eb < 2 ^ e -> Zmod.to_Z b = b2z sb * 2 ^ (f + e) + Eb * 2 ^ f + Mb ->
    Ea <> 2 ^ e - 1 -> (Ea <> 0 \/ Ma <> 0) -> Eb <> 2 ^ e - 1 -> (Eb <> 0 \/ Mb <> 0) ->
    let r := evalLetExpr (normRound false e f type (2 * f + 2) (xorb sa sb)
               (evalExpr (Add [Var type (Bit (e + 3)) (uExp (unp a)); Var type (Bit (e + 3)) (uExp (unp b));
                               cst (e + 3) (1 - expOff false e)]))
               (evalExpr (sigProduct f type (uSig (unp a)) (uSig (unp b)))) false rm) in
    r.(Fst) = ofB (BinarySingleNaN.Bmult (modeOf rm) (toB a) (toB b)) /\
    r.(Snd).(Fst) = finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
                      (BinarySingleNaN.B2R (toB a) * BinarySingleNaN.B2R (toB b)).
  Proof.
    intros rm a b sa Ea Ma sb Eb Mb HMa HEa Ha HMb HEb Hb HnA HzA HnB HzB r.
    pose proof HeM as He0.
    pose proof (fin_facts a sa Ea Ma HMa HEa Ha HnA HzA) as FA; cbv zeta in FA.
    pose proof (fin_facts b sb Eb Mb HMb HEb Hb HnB HzB) as FB; cbv zeta in FB.
    set (Xa := Zmod.signed (uExp (unp a))) in *. set (Sa := Zmod.to_Z (uSig (unp a))) in *.
    set (Xb := Zmod.signed (uExp (unp b))) in *. set (Sb := Zmod.to_Z (uSig (unp b))) in *.
    destruct FA as (HSa & HXa & HVa & HFa & HGa). destruct FB as (HSb & HXb & HVb & HFb & HGb).
    assert (HP : 2 ^ e = 2 * 2 ^ (e - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (HP1 : 1 <= 2 ^ (e - 1)) by (pose proof (Z.pow_le_mono_r 2 0 (e - 1)); lia).
    assert (HF1 : 2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (HF4 : 4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (HE2 : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    unfold fpEmin, fpEmax, fpBias in HXa, HXb.
    (* the product and its exponent *)
    set (prod := evalExpr (sigProduct f type (uSig (unp a)) (uSig (unp b)))) in r.
    assert (Hprod : Zmod.to_Z prod = Sa * Sb) by apply prod_val.
    set (xP := evalExpr (Add [Var type (Bit (e + 3)) (uExp (unp a)); Var type (Bit (e + 3)) (uExp (unp b));
                              cst (e + 3) (1 - expOff false e)])) in r.
    assert (HxP : Zmod.signed xP = Xa + Xb + 1) by (apply xP_val; fold Xa Xb; lia).
    assert (HW2 : 2 ^ (2 * f + 2) = 2 ^ (f + 1) * 2 ^ (f + 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HWv : 0 < Sa * Sb < 2 ^ (2 * f + 2)) by (rewrite HW2; split; [nia | apply Z.mul_lt_mono_nonneg; lia]).
    assert (HfW : 2 * f + 2 < 2 ^ (e + 2)) by lia.
    pose proof (normRound_eval e f He0 Hf (2 * f + 2) (xorb sa sb) xP prod false rm ltac:(lia) HfW ltac:(lia) ltac:(lia)) as HN.
    cbv zeta in HN. unfold r; rewrite HN; clear HN.
    rewrite Hprod, HxP.
    set (k := 2 * f + 2 - 1 - Z.log2 (Sa * Sb)). set (d := 2 * f + 2 - (f + 3)).
    destruct (norm_window f Hf (2 * f + 2) (Sa * Sb) ltac:(lia) HWv) as (Hk & HN1 & HN2); fold k d in Hk, HN1, HN2.
    set (top := Sa * Sb * 2 ^ k / 2 ^ d) in *.
    set (st2 := false || negb ((Sa * Sb * 2 ^ k) mod 2 ^ d =? 0)).
    pose proof (roundPack_Z e f He0 Hf Hpe (xorb sa sb) (Zmod.of_Z _ (Xa + Xb + 1 - k)) (Zmod.of_Z _ top) st2 rm) as HR.
    cbv zeta in HR. rewrite HR; clear HR. cbn [Fst Snd].
    assert (HX' : Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) (Xa + Xb + 1 - k)) = Xa + Xb + 1 - k).
    { apply signed_of_Z_small; [lia |]. replace (e + 3 - 1) with (e + 2) by lia. lia. }
    assert (HS' : Zmod.to_Z (Zmod.of_Z (2 ^ (f + 3)) top) = top) by (apply tz_ofZ; lia).
    rewrite HX', HS'.
    (* the exact product as a real *)
    set (v := (BinarySingleNaN.B2R (toB a) * BinarySingleNaN.B2R (toB b))%R).
    assert (Hv : v = cond_Ropp (xorb sa sb) (F2R (Float radix2 (Sa * Sb) (Xa + Xb - 2 * f)))).
    { unfold v; rewrite HVa, HVb. unfold F2R; cbn [Fnum Fexp]. rewrite mult_IZR.
      replace (Xa + Xb - 2 * f) with ((Xa - f) + (Xb - f)) by lia. rewrite bpow_plus.
      destruct sa, sb; cbn [cond_Ropp xorb]; ring. }
    assert (Hpos : (0 < F2R (Float radix2 (Sa * Sb) (Xa + Xb - 2 * f)))%R).
    { unfold F2R; cbn [Fnum Fexp]. apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]. }
    assert (Hs : Rlt_bool v 0 = xorb sa sb) by (rewrite Hv; apply Rlt_bool_cond_Ropp; exact Hpos).
    assert (Hin0 : inbetween_float radix2 (Sa * Sb) (Xa + Xb + 1 - (2 * f + 2 - 1)) (Rabs v) loc_Exact).
    { constructor. rewrite Hv, abs_cond_Ropp, Rabs_pos_eq by lra. f_equal; f_equal; lia. }
    destruct (norm_loc f Hf (2 * f + 2) (Sa * Sb) (Xa + Xb + 1) false v loc_Exact ltac:(lia) HWv Hin0
                ltac:(split; reflexivity) ltac:(discriminate)) as [l2 [Hin Hl]].
    fold k d top st2 in Hin, Hl.
    assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (apply (bits.unsigned_range rm); lia).
    assert (HS : 2 ^ (f + 2) <= top < 2 ^ (f + 3)) by exact HN2.
    split.
    - (* the result *)
      assert (HT : toB (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) (xorb sa sb) (Xa + Xb + 1 - k) top st2)) =
                   BinarySingleNaN.Bmult (modeOf rm) (toB a) (toB b)).
      { apply (rp_result e f Hf Hpe (Zmod.to_Z rm) (xorb sa sb) (Xa + Xb + 1 - k) top st2 v l2 Hrm HS Hin Hl Hs).
        pose proof (BinarySingleNaN.Bmult_correct (f + 1) (2 ^ (e - 1)) _ _ (modeOf rm) (toB a) (toB b)) as BC.
        fold v in BC. rewrite HGa, HGb, HFa, HFb in BC.
        change (modeZ (Zmod.to_Z rm)) with (modeOf rm).
        match goal with |- if Rlt_bool ?x ?y then _ else _ => destruct (Rlt_bool x y) end.
        - destruct BC as (B1 & B2 & B3). refine (conj B1 (conj B2 _)). apply B3.
          apply (is_nan_of_correct _ (modeOf rm) (xorb sa sb)); left; exact B2.
        - exact BC. }
      rewrite <- HT. symmetry. apply ofB_toB. rewrite HT.
      pose proof (BinarySingleNaN.Bmult_correct (f + 1) (2 ^ (e - 1)) _ _ (modeOf rm) (toB a) (toB b)) as BC.
      rewrite HGa, HGb, HFa, HFb in BC.
      match type of BC with if Rlt_bool ?x ?y then _ else _ => destruct (Rlt_bool x y) end;
        apply (is_nan_of_correct _ (modeOf rm) (xorb sa sb)); [left; apply BC | right; exact BC].
    - (* the flags *)
      unfold finiteFlags. fold v.
      change (modeOf rm) with (modeZ (Zmod.to_Z rm)).
      rewrite (rp_flags e f Hf Hpe (Zmod.to_Z rm) (xorb sa sb) (Xa + Xb + 1 - k) top st2 v l2 Hrm HS Hin Hl Hs).
      reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * FMUL
   * --------------------------------------------------------------------------- *)

  Definition clsTriple (x : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) : bool * bool * bool :=
    match x with
    | BinarySingleNaN.B754_zero _ => (true, false, false)
    | BinarySingleNaN.B754_infinity _ => (false, true, false)
    | BinarySingleNaN.B754_nan => (false, false, true)
    | BinarySingleNaN.B754_finite _ _ _ _ => (false, false, false)
    end.

  Lemma cls_bools : forall x s E M, clsP x s E M ->
    ((E =? 0) && (M =? 0), (E =? 2 ^ e - 1) && (M =? 0), (E =? 2 ^ e - 1) && negb (M =? 0)) = clsTriple x.
  Proof.
    intros x s E M C. pose proof HeM as He0.
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    destruct x; cbn [clsP clsTriple] in *.
    - destruct C as (_ & -> & ->). rewrite Z.eqb_refl. replace (0 =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - destruct C as (_ & -> & ->). rewrite !Z.eqb_refl. replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - destruct C as (-> & HM). rewrite Z.eqb_refl. replace (M =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - destruct C as (_ & Hn & Hz & _). replace (E =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); try lia; reflexivity.
  Qed.

  Lemma mkFlags_eval : forall nv dz ov uf nx : bool,
    evalExpr (mkFlags type (ConstBool nv) (ConstBool dz) (ConstBool ov) (ConstBool uf) (ConstBool nx)) = mkFl nv dz ov uf nx.
  Proof. intros [|] [|] [|] [|] [|]; vm_compute; reflexivity. Qed.

  Theorem fmul_flocq_holds : fmul_flocq.
  Proof.
    intros rm a b. pose proof HeM as He0.
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    rewrite fmul_core_res, fmul_core_flags. unfold mulCore. rewrite !flip0, !mulFinish_V. unfold mulV. cbv zeta.
    rewrite (u_sign e f He0 Hf a sa Ea Ma HMa HEa Ha), (u_zero e f He0 Hf a sa Ea Ma HMa HEa Ha),
            (u_inf e f He0 Hf a sa Ea Ma HMa HEa Ha), (u_nan e f He0 Hf a sa Ea Ma HMa HEa Ha),
            (u_snan e f He0 Hf a sa Ea Ma HMa HEa Ha).
    rewrite (u_sign e f He0 Hf b sb Eb Mb HMb HEb Hb), (u_zero e f He0 Hf b sb Eb Mb HMb HEb Hb),
            (u_inf e f He0 Hf b sb Eb Mb HMb HEb Hb), (u_nan e f He0 Hf b sb Eb Mb HMb HEb Hb),
            (u_snan e f He0 Hf b sb Eb Mb HMb HEb Hb).
    unfold mulFlags. rewrite (isSNaN_eq a sa Ea Ma HMa HEa Ha), (isSNaN_eq b sb Eb Mb HMb HEb Hb).
    pose proof (cls a sa Ea Ma HMa HEa Ha) as Ca. pose proof (cls b sb Eb Mb HMb HEb Hb) as Cb.
    pose proof (cls_bools _ _ _ _ Ca) as Ta. pose proof (cls_bools _ _ _ _ Cb) as Tb.
    pose proof (mul_finite rm a b sa Ea Ma sb Eb Mb HMa HEa Ha HMb HEb Hb) as MF.
    destruct (toB a) as [xa | xa | | xa ma ea Hba] eqn:TA; destruct (toB b) as [xb | xb | | xb mb eb Hbb] eqn:TB;
      cbn [clsP clsTriple] in Ca, Cb, Ta, Tb; injection Ta as Ta1 Ta2 Ta3; injection Tb as Tb1 Tb2 Tb3;
      rewrite ?Ta1, ?Ta2, ?Ta3, ?Tb1, ?Tb2, ?Tb3; cbn [orb andb negb Fst Snd].
    all: try (destruct Ca as (_ & Hna & Hza & _); destruct Cb as (_ & Hnb & Hzb & _); exact (MF Hna Hza Hnb Hzb)).
    all: try (destruct Ca as [-> _]); try (destruct Cb as [-> _]); cbn [BinarySingleNaN.Bmult]; rewrite ?mkFlags_eval.
    all: split; [first [symmetry; apply ofB_nan | symmetry; apply ofB_inf | symmetry; apply ofB_zero] | try reflexivity].
    all: rewrite ?orb_false_r; reflexivity.
  Qed.
End Mul.
