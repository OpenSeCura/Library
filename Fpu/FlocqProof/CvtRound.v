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
 * Zfa FROUND / FROUNDNX against Flocq's `Bnearbyint` (`CvtRound.v`).
 *
 * `frndRef rm nx a` is the reference core (`FpCoreRef.fpuComputeRef`) on a decoded FROUND
 * (`nx`: FROUNDNX).  `fround_flocq_holds`: its result is Flocq's `BinarySingleNaN.Bnearbyint`
 * (round to an integral value with the rounding mode; NaN encoded as the RISC-V canonical NaN) and
 * its flags are NV for a signaling NaN and, for FROUNDNX only, NX when the result differs from
 * the operand.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul CvtIF.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Lemma mkFlags_eval : forall nv dz ov uf nx,
  evalExpr (mkFlags type (ConstBool nv) (ConstBool dz) (ConstBool ov) (ConstBool uf) (ConstBool nx)) = mkFl nv dz ov uf nx.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.

Section Round.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).

  Local Instance precGt : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLt : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  Definition opRnd (nx : bool) : type FpOpDK :=
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (false ,, (true ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (false ,, (false ,, (nx ,, tt)))))))))))))))))))))).

  Definition reqRnd (nx : bool) (rm : bits 3) (a : bits W) : type (FpReqK e f xlen) :=
    (opRnd nx ,, (rm ,, (a ,, (Zmod.zero ,, (Zmod.zero ,, (Zmod.zero ,, tt)))))).

  Definition frndRef (rm : bits 3) (nx : bool) (a : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqRnd nx rm a)).

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uExp := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSig := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst)).

  (* `fpRound false`, transcribed. *)
  Definition rndV (rm : bits 3) (nx : bool) (a : bits W) (ua : type (FpUnpK e f)) : type (FpOutK e f) :=
    let s := uSign ua in
    let xv := uExp ua in
    let intg := evalExpr (Slt (cst (e + 3) (f - 1 + expOff false e)) (Var type (Bit (e + 3)) xv)) in
    let shR0 := evalExpr (Sub (cst (e + 3) (f + expOff false e)) (Var type (Bit (e + 3)) xv)) in
    let shR := evalExpr (ITE (Ult (Var type (Bit (e + 3)) shR0) (cst (e + 3) (f + 4))) (Var type (Bit (e + 3)) shR0) (cst (e + 3) (f + 4))) in
    let base := evalExpr (Sll (zext (f + 1) (f + 4) (Var type (Bit (f + 1)) (uSig ua))) (cst (f + 4) 2)) in
    let nn := evalExpr (Srl (Var type (Bit (f + 4)) base) (Var type (Bit (e + 3)) shR)) in
    let stk := evalExpr (isNotZero (And [Var type (Bit (f + 4)) base; Not (Sll (cst (f + 4) (-1)) (Var type (Bit (e + 3)) shR))])) in
    let lsb := evalExpr (bitSet (ty := type) nn 2) in
    let g := evalExpr (bitSet (ty := type) nn 1) in
    let r := evalExpr (Or [bitSet (ty := type) nn 0; Var type Bool stk]) in
    let inc := evalExpr (roundInc type rm s lsb g r) in
    let inexact := evalExpr (Or [Var type Bool g; Var type Bool r]) in
    let m := evalExpr (Add [Srl (Var type (Bit (f + 4)) nn) (cst (f + 4) 2); ITE (Var type Bool inc) (cst (f + 4) 1) (cst (f + 4) 0)]) in
    if uNaN ua then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool (uSNaN ua)) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if (uInf ua || uZero ua) || intg then (a ,, (evalExpr (noFlags type) ,, tt))
    else ((evalLetExpr (normRound false e f type (f + 4) s (evalExpr (cst (e + 3) (f + 3 + expOff false e))) m false rm)).(Fst) ,,
          (evalExpr (mkFlags type (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool (nx && inexact))) ,, tt)).

  Lemma fpRound_V : forall rm nx a ua, evalLetExpr (fpRound false e f type rm nx a ua) = rndV rm nx a ua.
  Proof. intros; exact eq_refl. Qed.

  Lemma HeR : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  Local Abbreviation nbi rm a := (BinarySingleNaN.Bnearbyint (modeOf rm) (toB a)).

  (* IEEE flags of FROUND / FROUNDNX. *)
  Definition rndFlags (rm : bits 3) (nx : bool) (a : bits W) : bits 5 :=
    match toB a with
    | BinarySingleNaN.B754_nan => mkFl (isSNaN e f Hf Hpe a) false false false false
    | _ => mkFl false false false false
             (nx && negb (Req_bool (BinarySingleNaN.B2R (nbi rm a)) (BinarySingleNaN.B2R (toB a))))
    end.

  Definition fround_flocq : Prop :=
    forall rm nx a,
      (frndRef rm nx a) @% "res" = ofB (nbi rm a) /\ (frndRef rm nx a) @% "flags" = rndFlags rm nx a.

  Lemma frnd_res0 : forall rm nx a, (frndRef rm nx a) @% "res" = (evalLetExpr (fpRound false e f type rm nx a (unp a))).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma frnd_flags0 : forall rm nx a, (frndRef rm nx a) @% "flags" = (evalLetExpr (fpRound false e f type rm nx a (unp a))).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma frnd_res : forall rm nx a, (frndRef rm nx a) @% "res" = (rndV rm nx a (unp a)).(Fst).
  Proof. intros; rewrite frnd_res0, fpRound_V; reflexivity. Qed.

  Lemma frnd_flags : forall rm nx a, (frndRef rm nx a) @% "flags" = (rndV rm nx a (unp a)).(Snd).(Fst).
  Proof. intros; rewrite frnd_flags0, fpRound_V; reflexivity. Qed.

  Lemma rndFlags_fin : forall rm nx a, BinarySingleNaN.is_nan (toB a) = false ->
    rndFlags rm nx a = mkFl false false false false
      (nx && negb (Req_bool (BinarySingleNaN.B2R (nbi rm a)) (BinarySingleNaN.B2R (toB a)))).
  Proof. intros rm nx a H; unfold rndFlags; destruct (toB a); try reflexivity; discriminate H. Qed.

  (* The main case: a finite non-zero operand with unbiased exponent below `f`. *)
  Lemma rnd_main : forall rm nx a s E M,
    0 <= M < 2 ^ f -> 0 <= E < 2 ^ e -> Zmod.to_Z a = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    E <> 2 ^ e - 1 -> (E <> 0 \/ M <> 0) -> Zmod.signed (uExp (unp a)) <= f - 1 ->
    (rndV rm nx a (unp a)).(Fst) = ofB (nbi rm a) /\
    (rndV rm nx a (unp a)).(Snd).(Fst) =
      mkFl false false false false (nx && negb (Req_bool (BinarySingleNaN.B2R (nbi rm a)) (BinarySingleNaN.B2R (toB a)))).
  Proof.
    intros rm nx a s E M HM HE Ha Hn Hz HXf.
    pose proof HeR as He2.
    pose proof (fin_facts e f Hf Hpe a s E M HM HE Ha Hn Hz) as FF; cbv beta zeta in FF.
    destruct FF as (HSg & HX & HV & Hfin & Hsgn).
    pose proof (u_nan e f He2 Hf a s E M HM HE Ha) as Hun. pose proof (u_inf e f He2 Hf a s E M HM HE Ha) as Hui.
    pose proof (u_zero e f He2 Hf a s E M HM HE Ha) as Huz. pose proof (u_sign e f He2 Hf a s E M HM HE Ha) as Hus.
    replace ((E =? 2 ^ e - 1) && negb (M =? 0)) with false in Hun by (destruct (Z.eqb_spec E (2 ^ e - 1)); [lia | reflexivity]).
    replace ((E =? 2 ^ e - 1) && (M =? 0)) with false in Hui by (destruct (Z.eqb_spec E (2 ^ e - 1)); [lia | reflexivity]).
    replace ((E =? 0) && (M =? 0)) with false in Huz by (destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); try reflexivity; lia).
    set (v := BinarySingleNaN.B2R (toB a)) in *.
    assert (Hnbi := BinarySingleNaN.Bnearbyint_correct (f + 1) (2 ^ (e - 1)) _ (modeOf rm) (toB a)).
    fold v in Hnbi. destruct Hnbi as (Hnv & Hnf & Hns). rewrite Hfin in Hnf.
    assert (Hnn : BinarySingleNaN.is_nan (nbi rm a) = false) by (destruct (nbi rm a); try reflexivity; discriminate Hnf).
    specialize (Hns Hnn). rewrite Hsgn in Hns.
    set (b := nbi rm a) in *. clearbody b.
    set (ua := unp a) in *. clearbody ua.
    destruct ua as [s0 [z0 [i0 [n0 [sn0 [xv [sig []]]]]]]]; cbn [Fst Snd] in *. subst s0 z0 i0 n0.
    set (X := Zmod.signed xv) in *. set (Sg := Zmod.to_Z sig) in *.
    assert (HXd : Zmod.signed xv = X) by reflexivity. assert (HSd : Zmod.to_Z sig = Sg) by reflexivity.
    clearbody X Sg.
    unfold fpEmin, fpEmax, fpBias in HX.
    assert (P8 : 2 ^ (e + 3) = 16 * 2 ^ (e - 1)) by (replace (e + 3) with ((e - 1) + 4) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Pf1 : 2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (Pf3 : 2 ^ (f + 3) = 8 * 2 ^ f) by (rewrite Z.pow_add_r by lia; change (2 ^ 3) with 8; lia).
    assert (Pf4 : 2 ^ (f + 4) = 16 * 2 ^ f) by (rewrite Z.pow_add_r by lia; change (2 ^ 4) with 16; lia).
    assert (Hfe : f < 2 ^ (e - 1)) by lia.
    assert (P2 : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Hp0 : 4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    unfold rndV; cbv zeta; cbn [Fst Snd].
    (* intg = false *)
    rewrite (slt_eval (e + 3)) by lia.
    change (evalExpr (Var type (Bit (e + 3)) xv)) with xv.
    change (evalExpr (cst (e + 3) (f - 1 + expOff false e))) with (Zmod.of_Z (2 ^ (e + 3)) (f - 1 + 0)).
    rewrite signed_k, HXd by lia.
    replace (f - 1 + 0 <? X) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbn [Fst Snd orb].
    (* the exponent difference *)
    match goal with |- context [evalExpr (Sub ?c ?d)] => set (shR0 := evalExpr (Sub c d)) end.
    assert (HshR0 : Zmod.to_Z shR0 = f - X).
    { unfold shR0. rewrite (sub_eval (e + 3)) by lia. cbn [evalExpr cst expOff]. rewrite Z.add_0_r.
      rewrite <- (Zmod.of_Z_signed xv), HXd, <- Zmod.of_Z_sub. apply tz_ofZ; lia. }
    clearbody shR0.
    match goal with |- context [evalExpr (ITE (Ult ?a ?b) ?c ?d)] => set (sh := evalExpr (ITE (Ult a b) c d)) end.
    assert (Hsh : Zmod.to_Z sh = Z.min (f - X) (f + 4)).
    { unfold sh. cbn [evalExpr cst]. rewrite HshR0, (tz_ofZ (e + 3) (f + 4)) by lia.
      destruct (Z.ltb_spec (f - X) (f + 4)); [rewrite HshR0; lia | rewrite tz_ofZ by lia; lia]. }
    clearbody sh.
    match goal with |- context [evalExpr (Sll (zext ?i ?o ?x) ?c)] => set (base := evalExpr (Sll (zext i o x) c)) end.
    assert (Hbase : Zmod.to_Z base = Sg * 4).
    { unfold base. cbn [evalExpr]. rewrite bits.unsigned_slu, unsigned_zext by lia. cbn [evalExpr cst].
      rewrite (tz_ofZ (f + 4) 2) by lia. rewrite HSd, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. apply Z.mod_small; lia. }
    clearbody base.
    set (D := Z.min (f - X) (f + 4)) in *.
    match goal with |- context [evalExpr (Srl (Var _ _ base) ?c)] => set (nn := evalExpr (Srl (Var _ _ base) c)) end.
    assert (Hnn' : Zmod.to_Z nn = Sg * 4 / 2 ^ D).
    { unfold nn. cbn [evalExpr]. rewrite tz_sru by lia. rewrite Hbase, Hsh; reflexivity. }
    clearbody nn.
    match goal with |- context [evalExpr (isNotZero ?t)] => set (stk := evalExpr (isNotZero t)) end.
    assert (Hstk : stk = negb ((Sg * 4) mod 2 ^ D =? 0)).
    { unfold stk. rewrite evalExpr_isNotZero_bits.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd evalNot cst].
      rewrite unsigned_and_m1_l by lia. rewrite tz_lowmask by (rewrite Hsh; lia).
      rewrite Hbase, Hsh; reflexivity. }
    clearbody stk. subst stk.
    rewrite !bitSet_testbit by lia. rewrite roundInc_eval, Hnn'.
    set (NN := Sg * 4 / 2 ^ D) in *.
    assert (HNN : 0 <= NN) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
    assert (HNNd : NN = Sg * 4 / 2 ^ D) by reflexivity. clearbody NN.
    remember (rmInc (Zmod.to_Z rm) s (Z.testbit NN 2) (Z.testbit NN 1) (Z.testbit NN 0 || negb ((Sg * 4) mod 2 ^ D =? 0))) as inc eqn:Hincd.
    (* the real side *)
    assert (Hpos : (0 < F2R (Float radix2 Sg (X - f)))%R) by (apply F2R_gt_0; cbn; lia).
    assert (Hs : Rlt_bool v 0 = s) by (rewrite HV; apply Rlt_bool_cond_Ropp; exact Hpos).
    assert (Hav : Rabs v = F2R (Float radix2 (Sg * 4) (X - f - 2))).
    { rewrite HV, abs_cond_Ropp, Rabs_pos_eq by lra. change 4 with (2 ^ 2). rewrite F2R_scale by lia. reflexivity. }
    assert (Hin0 : inbetween_float radix2 (Sg * 4) (X - f - 2) (Rabs v) loc_Exact) by (constructor; exact Hav).
    destruct (loc_shift (Rabs v) (Sg * 4) (X - f - 2) loc_Exact false (f - X) ltac:(lia) Hin0 ltac:(split; reflexivity))
      as (l1 & Hl1 & Hl1e).
    assert (Eq : Sg * 4 / 2 ^ (f - X) = NN /\ (Sg * 4) mod 2 ^ (f - X) = (Sg * 4) mod 2 ^ D).
    { rewrite HNNd; unfold D. destruct (Z.le_ge_cases (f - X) (f + 4)) as [Hd | Hd]; [rewrite Z.min_l by lia; split; reflexivity |].
      rewrite Z.min_r by lia.
      assert (2 ^ (f + 4) <= 2 ^ (f - X)) by (apply Z.pow_le_mono_r; lia).
      rewrite !Z.div_small, !Z.mod_small by lia; split; reflexivity. }
    destruct Eq as [E1 E2]; rewrite E1 in Hl1; rewrite E2 in Hl1e. cbn [orb] in Hl1e.
    pose proof (loc_drop2 _ _ _ _ _ Hl1 Hl1e) as Hloc.
    replace (X - f - 2 + (f - X) + 2) with 0 in Hloc by lia.
    assert (Hrm : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)); change (2 ^ 3) with 8 in *; lia).
    pose proof (round_at (FIX_exp 0) (Zmod.to_Z rm) s v (NN / 4) 0 _ _ Hrm Hs eq_refl Hloc) as Hr.
    rewrite <- testbit2_odd, <- Hincd in Hr by lia.
    change (modeOf rm) with (modeZ (Zmod.to_Z rm)) in Hnv. rewrite Hr in Hnv.
    set (Mi := NN / 4 + b2z inc) in *.
    assert (HMid : Mi = NN / 4 + b2z inc) by reflexivity. clearbody Mi.
    assert (HMi : 0 <= Mi <= 2 ^ f).
    { assert (NN / 4 < 2 ^ f).
      { rewrite HNNd, Z.div_div by (try apply Z.pow_pos_nonneg; lia). apply Z.div_lt_upper_bound; [apply Z.mul_pos_pos; [apply Z.pow_pos_nonneg |]; lia |].
        assert (2 ^ 1 <= 2 ^ D) by (apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in *.
        assert (2 ^ f * 2 <= 2 ^ f * 2 ^ D) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      assert (0 <= NN / 4) by (apply Z.div_pos; lia). rewrite HMid; destruct inc; cbn [b2z]; lia. }
    split.
    - (* the result *)
      match goal with |- context [evalExpr (Add [Srl ?a ?b'; ?c])] => set (m := evalExpr (Add [Srl a b'; c])) end.
      assert (Hm : Zmod.to_Z m = Mi).
      { unfold m. cbn [evalExpr fold_left map cst evalOrBinary evalBinary KindCustomInd getDefault orb].
        rewrite !Zmod.unsigned_add, Zmod.unsigned_0. rewrite !bitSet_testbit by lia.
        rewrite (tz_ofZ (f + 4) 2), tz_sru by lia. rewrite Hnn'. change (2 ^ 2) with 4.
        rewrite HMid in *; rewrite <- Hincd.
        assert (Hb01 : 0 <= b2z inc <= 1) by (destruct inc; cbn; lia).
        clear Hincd. destruct inc; cbn [b2z] in *; rewrite tz_ofZ by lia;
          assert (0 <= NN / 4) by (apply Z.div_pos; lia); assert (NN / 4 < 2 ^ (f + 4)) by lia; rewrite Z.add_0_l, (Z.mod_small (NN / 4)) by lia; apply Z.mod_small; lia. }
      clearbody m.
      change (evalExpr (cst (e + 3) (f + 3 + expOff false e))) with (Zmod.of_Z (2 ^ (e + 3)) (f + 3 + 0)).
      rewrite Z.add_0_r.
      destruct (Z.eq_dec Mi 0) as [HM0 | HM0].
      + rewrite normRound_zero by lia. cbn [Fst].
        assert (Hb0 : b = BinarySingleNaN.B754_zero s).
        { apply BinarySingleNaN.B2R_Bsign_inj; [exact Hnf | reflexivity | | exact Hns].
          rewrite Hnv, HM0. destruct s; cbn; unfold F2R; cbn; ring. }
        rewrite Hb0, (ofB_zero e f Hf Hpe); reflexivity.
      + assert (Hx1 : Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) (f + 3)) = f + 3) by (apply signed_k; lia).
        pose proof (normRound_eval e f He2 Hf (f + 4) s (Zmod.of_Z _ (f + 3)) m false rm ltac:(lia)
                      ltac:(lia) ltac:(lia) ltac:(rewrite Hx1; lia)) as HR.
        cbv zeta in HR; rewrite HR; clear HR.
        rewrite (roundPack_Z e f He2 Hf Hpe). cbn [Fst]. rewrite Hx1, Hm.
        set (k := f + 4 - 1 - Z.log2 Mi). set (d := f + 4 - (f + 3)).
        destruct (norm_window f Hf (f + 4) Mi ltac:(lia) ltac:(lia)) as (Hk & HNw & HSw); fold k d in Hk, HNw, HSw.
        rewrite signed_k, tz_ofZ by lia.
        assert (Hbv : BinarySingleNaN.B2R b = cond_Ropp s (F2R (Float radix2 Mi 0))) by (rewrite Hnv, F2R_cond_Zopp; reflexivity).
        assert (HMpos : (0 < F2R (Float radix2 Mi 0))%R) by (apply F2R_gt_0; cbn; lia).
        assert (Hin : inbetween_float radix2 Mi (f + 3 - (f + 4 - 1)) (Rabs (BinarySingleNaN.B2R b)) loc_Exact).
        { constructor. rewrite Hbv, abs_cond_Ropp, Rabs_pos_eq by lra. f_equal; f_equal; lia. }
        destruct (norm_loc f Hf (f + 4) Mi (f + 3) false (BinarySingleNaN.B2R b) loc_Exact ltac:(lia) ltac:(lia) Hin
                    ltac:(split; reflexivity) ltac:(discriminate)) as (l2 & Hin2 & Hl2); fold k d in Hin2, Hl2.
        assert (Hsb : Rlt_bool (BinarySingleNaN.B2R b) 0 = s) by (rewrite Hbv; apply Rlt_bool_cond_Ropp; exact HMpos).
        assert (Hbn : toB (Zmod.of_Z _ (rpRes e f (Zmod.to_Z rm) s (f + 3 - k) (Mi * 2 ^ k / 2 ^ d)
                                         (false || negb ((Mi * 2 ^ k) mod 2 ^ d =? 0)))) = b).
        { apply (rp_result e f Hf Hpe _ _ _ _ _ (BinarySingleNaN.B2R b) l2 Hrm HSw Hin2 Hl2 Hsb).
          rewrite round_generic by (try apply valid_rnd_round_mode; apply BinarySingleNaN.generic_format_B2R).
          rewrite Rlt_bool_true by apply BinarySingleNaN.abs_B2R_lt_emax.
          split; [reflexivity | split; [exact Hnf | exact Hns]]. }
        rewrite <- Hbn, ofB_toB; [reflexivity |]. rewrite Hbn; exact Hnn.
    - (* the flags *)
      rewrite mkFlags_eval. cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault orb].
      f_equal. f_equal. f_equal. rewrite !bitSet_testbit by lia. rewrite Hnn', Hnv, HMid.
      rewrite (exact_iff s v (NN / 4) 0 _ (b2z inc) Hs Hloc ltac:(apply Z.div_pos; lia)).
      + destruct (Z.testbit NN 1), (Z.testbit NN 0 || negb ((Sg * 4) mod 2 ^ D =? 0)); reflexivity.
      + rewrite Hincd; destruct (Z.testbit NN 1), (Z.testbit NN 0 || negb ((Sg * 4) mod 2 ^ D =? 0)); cbn [locOf];
          intros H; try discriminate H; rewrite rmInc_exact; reflexivity.
      + destruct inc; cbn [b2z]; lia.
  Qed.
  (* An operand with unbiased exponent at least `f` is already integral. *)
  Lemma nbi_integral : forall rm a s E M,
    0 <= M < 2 ^ f -> 0 <= E < 2 ^ e -> Zmod.to_Z a = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    E <> 2 ^ e - 1 -> (E <> 0 \/ M <> 0) -> f <= Zmod.signed (uExp (unp a)) -> nbi rm a = toB a.
  Proof.
    intros rm a s E M HM HE Ha Hn Hz HXf.
    pose proof (fin_facts e f Hf Hpe a s E M HM HE Ha Hn Hz) as FF; cbv beta zeta in FF.
    destruct FF as (HSg & HX & HV & Hfin & Hsgn).
    match type of HV with context [F2R (Float radix2 ?a (?b - f))] => set (Sg := a) in *; set (X := b) in * end.
    clearbody X Sg.
    destruct (BinarySingleNaN.Bnearbyint_correct (f + 1) (2 ^ (e - 1)) _ (modeOf rm) (toB a)) as (Hnv & Hnf & Hns).
    rewrite Hfin in Hnf.
    assert (Hnn : BinarySingleNaN.is_nan (nbi rm a) = false)
      by (revert Hnf; destruct (BinarySingleNaN.Bnearbyint (modeOf rm) (toB a)); intros Hnf; try reflexivity; discriminate Hnf).
    apply BinarySingleNaN.B2R_Bsign_inj; [exact Hnf | exact Hfin | | exact (Hns Hnn)].
    rewrite Hnv. apply round_generic; [apply valid_rnd_round_mode |]. apply generic_format_FIX.
    exists (Float radix2 (cond_Zopp s (Sg * 2 ^ (X - f))) 0); [| reflexivity].
    rewrite HV, F2R_cond_Zopp. f_equal. rewrite <- (F2R_scale Sg (X - f) (X - f)) by lia. f_equal; f_equal; lia.
  Qed.

  Lemma noFlags_eval : evalExpr (noFlags type) = mkFl false false false false false.
  Proof. vm_compute; reflexivity. Qed.

  Theorem fround_flocq_holds : fround_flocq.
  Proof.
    intros rm nx a. rewrite frnd_res, frnd_flags.
    pose proof HeR as He2.
    destruct (split_fields e f Hf Hpe a) as (s & E & M & HM & HE & Ha).
    pose proof (cls e f Hf Hpe a s E M HM HE Ha) as C.
    pose proof (u_nan e f He2 Hf a s E M HM HE Ha) as Hun. pose proof (u_inf e f He2 Hf a s E M HM HE Ha) as Hui.
    pose proof (u_zero e f He2 Hf a s E M HM HE Ha) as Huz. pose proof (u_snan e f He2 Hf a s E M HM HE Ha) as Hus.
    pose proof (isSNaN_eq e f Hf Hpe a s E M HM HE Ha) as Hsn.
    assert (Hnb : BinarySingleNaN.is_nan (toB a) = false -> a = ofB (toB a)) by (intros H; symmetry; apply ofB_toB; exact H).
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    destruct (Z.eq_dec E (2 ^ e - 1)) as [HE1 | HE1]; [destruct (Z.eq_dec M 0) as [HM0 | HM0] |].
    - (* infinity *)
      rewrite HE1, HM0, Z.eqb_refl in Hun, Hui. cbn [andb negb] in Hun, Hui.
      unfold rndV, rndFlags; cbv zeta. rewrite Hun, Hui. cbn [orb]. cbv iota. cbn [Fst Snd].
      destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
      split; [cbn [Fst]; apply Hnb; reflexivity | cbn [Fst Snd]].
      rewrite noFlags_eval, Req_bool_true by reflexivity. rewrite andb_false_r; reflexivity.
    - (* NaN *)
      rewrite HE1, Z.eqb_refl in Hun, Hus, Hsn. replace (M =? 0) with false in Hun, Hus, Hsn by (symmetry; apply Z.eqb_neq; exact HM0).
      cbn [andb negb] in Hun, Hus, Hsn.
      unfold rndV, rndFlags; cbv zeta. rewrite Hun. cbv iota. cbn [Fst Snd].
      destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
      rewrite mkFlags_eval, Hus, Hsn, <- (ofB_nan e f Hf Hpe). split; reflexivity.
    - replace ((E =? 2 ^ e - 1) && negb (M =? 0)) with false in Hun by (destruct (Z.eqb_spec E (2 ^ e - 1)); [lia | reflexivity]).
      replace ((E =? 2 ^ e - 1) && (M =? 0)) with false in Hui by (destruct (Z.eqb_spec E (2 ^ e - 1)); [lia | reflexivity]).
      assert (Hzd : (E = 0 /\ M = 0) \/ (E <> 0 \/ M <> 0)) by lia.
      destruct Hzd as [[HE0 HM0] | Hz].
      + (* zero *)
        rewrite HE0, HM0 in Huz. change ((0 =? 0) && (0 =? 0)) with true in Huz.
        unfold rndV, rndFlags; cbv zeta. rewrite Hun, Hui, Huz. cbn [orb]. cbv iota. cbn [Fst Snd].
        destruct (toB a) as [s' | s' | | s' m' ex' Hb'] eqn:Hb; cbn [clsP] in C; try lia.
        split; [cbn [Fst]; apply Hnb; reflexivity | cbn [Fst Snd]].
        rewrite noFlags_eval, Req_bool_true by reflexivity. rewrite andb_false_r; reflexivity.
      + replace ((E =? 0) && (M =? 0)) with false in Huz by (destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); try reflexivity; lia).
        assert (Hn0 : BinarySingleNaN.is_nan (toB a) = false)
          by (destruct (toB a); cbn [clsP] in C; try reflexivity; lia).
        rewrite rndFlags_fin by exact Hn0.
        destruct (Z_le_gt_dec f (Zmod.signed (uExp (unp a)))) as [Hi | Hi].
        * rewrite (nbi_integral rm a s E M HM HE Ha HE1 Hz Hi).
          unfold rndV; cbv zeta. rewrite Hun, Hui, Huz. cbn [orb].
          rewrite (slt_eval (e + 3)) by lia.
          change (evalExpr (Var type (Bit (e + 3)) (uExp (unp a)))) with (uExp (unp a)).
          change (evalExpr (cst (e + 3) (f - 1 + expOff false e))) with (Zmod.of_Z (2 ^ (e + 3)) (f - 1 + 0)).
          rewrite signed_k by (pose proof (Z.pow_le_mono_r 2 0 (e - 1)); lia).
          match goal with |- context [f - 1 + 0 <? ?t] =>
            replace (f - 1 + 0 <? t) with true by (symmetry; apply Z.ltb_lt; change t with (Zmod.signed (uExp (unp a))); cbv beta in Hi |- *; lia) end.
          cbn [orb]. cbv iota. cbn [Fst Snd]. rewrite Req_bool_true by reflexivity. rewrite andb_false_r, noFlags_eval.
          split; [apply Hnb; exact Hn0 | reflexivity].
        * exact (rnd_main rm nx a s E M HM HE Ha HE1 Hz ltac:(cbv beta in Hi |- *; lia)).
  Qed.
End Round.
