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
 * The staged FPU units compute exactly the spec (`FpuUnitsProof.v`).
 *
 * For each unit, `finish (step^n (init req)) = spec req` (`*_StageValAt_spec`), and the generic
 * controller theorems of `ImplStagedProof.v` instantiated for the unit.
 * - Square root: `sqrtSpec` is literally `sqrtFinish (sqrtStep^(f+3) (sqrtInit req))`.
 * - Pipe: after `mul_stages` stages the multiplier accumulator holds the significand product, so
 *   `pipeFinish` = `pipeFinishCore info (sigProduct ..)` = `pipeSpec`.
 * - Divide: the restoring recurrence keeps `siga * 2^k = 2 * quot * sigb + rem` with
 *   `rem < 2 * sigb`; after `f + 3` steps `quot` and `rem <> 0` are the spec's `Div` and `Rem <> 0`.
 * The finish functions (`pipeFinishCore`, `divFinishCore`, `sqrtFinish`) are never unfolded.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Fpu Require Import FpUtil FpCore IntMul ImplStaged ImplFpuUnits.
From Fpu Require Import IntMulProof ImplStagedProof FpUtilLemmas.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. SQUARE-ROOT UNIT
 * =========================================================================== *)

Section SqrtProof.
  Variable e f xlen wlen : Z.

  Lemma sqrtIter_succ_r : forall n s,
    evalLetExpr (sqrtIter e f type (S n) s) =
    evalLetExpr (sqrtStep e f type (evalLetExpr (sqrtIter e f type n s))).
  Proof.
    induction n as [| n IH]; intros s.
    - reflexivity.
    - change (evalLetExpr (sqrtIter e f type (S (S n)) s))
        with (evalLetExpr (sqrtIter e f type (S n) (evalLetExpr (sqrtStep e f type s)))).
      rewrite IH; reflexivity.
  Qed.

  Lemma StageValAt_sqrt : forall n req,
    StageValAt (sqrtInit true e f xlen) (sqrtStep e f) n req =
    evalLetExpr (sqrtIter e f type n (evalLetExpr (sqrtInit true e f xlen type req))).
  Proof.
    induction n as [| n IH]; intros req; cbn [StageValAt].
    - reflexivity.
    - rewrite IH, sqrtIter_succ_r; reflexivity.
  Qed.

  Theorem Sqrt_StageValAt_spec : forall req,
    evalLetExpr (sqrtFinish true e f type (StageValAt (sqrtInit true e f xlen) (sqrtStep e f) (sqrtSteps f) req)) =
    evalLetExpr (sqrtSpec true e f xlen type req).
  Proof.
    intros req; rewrite StageValAt_sqrt.
    unfold sqrtSpec; cbn [evalLetExpr]; reflexivity.
  Qed.
End SqrtProof.

(* ===========================================================================
 * 2. PIPE UNIT
 * =========================================================================== *)

Section PipeProof.
  Variable e f xlen wlen : Z.
  Variable mul_stages mul_bps : nat.

  Local Abbreviation mw := (mul_stages * mul_bps)%nat.
  Local Abbreviation dm := (dataLen mw).
  Local Abbreviation SK := (PipeStateK e f xlen mw).
  Local Abbreviation init := (pipeInit e f xlen mul_stages mul_bps).
  Local Abbreviation step := (pipeStep e f xlen mul_stages mul_bps).
  Local Abbreviation finish := (pipeFinish e f xlen wlen mul_stages mul_bps).

  Hypothesis H_mw_pos : (0 < mw)%nat.
  Hypothesis H_f : 0 <= f.
  Hypothesis H_fit : f + 1 <= dm.

  (* The multiplier operands built by `pipeInit`. *)
  Definition pipeOp1 (info : type (PipeInfoK e f xlen)) : bits dm :=
    evalExpr (zext (f + 1) dm (Var type (Bit (f + 1)) (info @% "ua" @% "sig"))).
  Definition pipeOp2 (info : type (PipeInfoK e f xlen)) : bits dm :=
    evalExpr (zext (f + 1) dm (Var type (Bit (f + 1)) (info @% "ub" @% "sig"))).
  Definition pipeExt2 (info : type (PipeInfoK e f xlen)) : bits (dm + dm) :=
    evalExpr (ZeroExtend dm (Var type (Bit dm) (pipeOp2 info))).

  (* Multiplier state after `n` bits. *)
  Definition pipeCoreAt (n : nat) (info : type (PipeInfoK e f xlen)) : type (MulCoreState dm) :=
    evalLetExpr (@mulMultiStep mw type n (pipeOp1 info) (pipeExt2 info) Zmod.zero).

  Lemma pipeInit_eval : forall req,
    let info := evalLetExpr (pipeInfoOf true e f xlen type req) in
    evalLetExpr (init type req) = (info ,, (pipeOp1 info ,, (pipeExt2 info ,, (Zmod.zero ,, tt)))).
  Proof. intros req info; timeout 20 reflexivity. Qed.

  Lemma pipeStep_eval : forall info sh ext acc,
    evalLetExpr (step type (info ,, (sh ,, (ext ,, (acc ,, tt))))) =
    let core := evalLetExpr (@mulMultiStep mw type mul_bps sh ext acc) in
    (info ,, (core @% "shiftOp" ,, (ext ,, (core @% "mulAcc" ,, tt)))).
  Proof. intros; timeout 20 reflexivity. Qed.

  Lemma pipeFinish_eval : forall info sh ext acc,
    evalLetExpr (finish type (info ,, (sh ,, (ext ,, (acc ,, tt))))) =
    evalLetExpr (pipeFinishCore true e f xlen wlen type info
                   (evalExpr (trunc (dm + dm) (2 * f + 2) (Var type (Bit (dm + dm)) acc)))).
  Proof.
    intros; unfold pipeFinish; cbn [evalLetExpr].
    apply f_equal; apply (f_equal2 (pipeFinishCore true e f xlen wlen type)); [timeout 20 reflexivity |].
    apply evalExpr_trunc_congr; reflexivity.
  Qed.

  Lemma pipeSpec_eval : forall req,
    let info := evalLetExpr (pipeInfoOf true e f xlen type req) in
    evalLetExpr (pipeSpec true e f xlen wlen type req) =
    evalLetExpr (pipeFinishCore true e f xlen wlen type info
                   (evalExpr (sigProduct f type (info @% "ua" @% "sig") (info @% "ub" @% "sig")))).
  Proof.
    intros req info; unfold pipeSpec; cbn [evalLetExpr].
    apply f_equal; apply (f_equal2 (pipeFinishCore true e f xlen wlen type)); timeout 20 reflexivity.
  Qed.

  Lemma StageValAt_pipe : forall k req,
    let info := evalLetExpr (pipeInfoOf true e f xlen type req) in
    let core := pipeCoreAt (k * mul_bps) info in
    StageValAt init step k req =
    (info ,, (core @% "shiftOp" ,, (pipeExt2 info ,, (core @% "mulAcc" ,, tt)))).
  Proof.
    induction k as [| k IH]; intros req info core; cbn [StageValAt].
    - rewrite pipeInit_eval; reflexivity.
    - rewrite (IH req); fold info.
      rewrite pipeStep_eval.
      unfold core, pipeCoreAt.
      replace (S k * mul_bps)%nat with (k * mul_bps + mul_bps)%nat by lia.
      rewrite (mulMultiStep_add mw (k * mul_bps) mul_bps).
      reflexivity.
  Qed.

  (* Truncating the core's product to `2p` bits gives the spec's significand product. *)
  Lemma pipe_product_eq : forall info,
    evalExpr (trunc (dm + dm) (2 * f + 2)
                (Var type (Bit (dm + dm)) ((pipeCoreAt mw info) @% "mulAcc"))) =
    evalExpr (sigProduct f type (info @% "ua" @% "sig") (info @% "ub" @% "sig")).
  Proof.
    intros info.
    set (A := info @% "ua" @% "sig").
    set (B := info @% "ub" @% "sig").
    unfold pipeCoreAt, pipeExt2.
    rewrite (mulMultiStep_eq_Mul mw H_mw_pos (pipeOp1 info) (pipeOp2 info)).
    apply Zmod.unsigned_inj.
    pose proof (bits_unsigned_bound (f + 1) A ltac:(lia)) as HA.
    pose proof (bits_unsigned_bound (f + 1) B ltac:(lia)) as HB.
    assert (Hdm : 0 < dm) by (unfold dataLen; lia).
    rewrite unsigned_trunc by lia.
    unfold sigProduct.
    cbn [evalExpr fold_left map].
    rewrite !Zmod.mul_1_l, !Zmod.unsigned_mul.
    rewrite !(unsigned_ZeroExtend dm dm) by lia.
    rewrite !(unsigned_zext (f + 1) (2 * f + 2)) by lia.
    rewrite !evalExpr_Var.
    unfold pipeOp1, pipeOp2; fold A B.
    rewrite !(unsigned_zext (f + 1) dm) by lia.
    rewrite !evalExpr_Var.
    assert (HAB : Zmod.unsigned A * Zmod.unsigned B < 2 ^ (2 * f + 2)).
    { replace (2 * f + 2) with ((f + 1) + (f + 1)) by lia.
      rewrite Z.pow_add_r by lia. nia. }
    assert (Hpow : 2 ^ (2 * f + 2) <= 2 ^ (dm + dm)) by (apply Z.pow_le_mono_r; lia).
    rewrite (Z.mod_small (Zmod.unsigned A * Zmod.unsigned B) (2 ^ (dm + dm))) by nia.
    rewrite (Z.mod_small (Zmod.unsigned A * Zmod.unsigned B) (2 ^ (2 * f + 2))) by nia.
    reflexivity.
  Qed.

  Theorem Pipe_StageValAt_spec : forall req,
    evalLetExpr (finish type (StageValAt init step mul_stages req)) =
    evalLetExpr (pipeSpec true e f xlen wlen type req).
  Proof.
    intros req.
    rewrite StageValAt_pipe, pipeFinish_eval, pipeSpec_eval.
    apply f_equal, f_equal.
    apply pipe_product_eq.
  Qed.
End PipeProof.

(* ===========================================================================
 * 3. UNPACKED SIGNIFICANDS HAVE THEIR TOP BIT SET
 * =========================================================================== *)

Lemma fpUnpack_sig_ge : forall (e f : Z) (x : type (FpBits e f)),
  0 <= f ->
  2 ^ f <= Zmod.unsigned ((evalLetExpr (fpUnpack true e f type x)) @% "sig").
Proof.
  intros e f x Hf.
  unfold fpUnpack; cbn [evalLetExpr].
  cbn [evalExpr readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple
       finNum Fst Snd mapDiffTuple fold_left map evalOrBinary evalBinary KindCustomInd getDefault cst].
  cbn [snd evalExpr].
  apply unsigned_or_pow2_ge; lia.
Qed.

(* ===========================================================================
 * 4. DIVIDE UNIT
 * =========================================================================== *)

Section DivProof.
  Local Open Scope Z_scope.
  Variable e f xlen wlen : Z.
  Hypothesis H_f : 0 <= f.

  Local Abbreviation init := (divInit e f xlen).
  Local Abbreviation step := (divStep e f).
  Local Abbreviation finish := (divFinish e f).

  (* One step of the restoring divider, as values. *)
  Definition dDenx (den : bits (f + 1)) : bits (f + 2) :=
    evalExpr (zext (f + 1) (f + 2) (Var type (Bit (f + 1)) den)).
  Definition dGe (rem : bits (f + 2)) (den : bits (f + 1)) : bool :=
    evalExpr (Not (Ult (Var type (Bit (f + 2)) rem) (Var type (Bit (f + 2)) (dDenx den)))).
  Definition dRem1 (rem : bits (f + 2)) (den : bits (f + 1)) : bits (f + 2) :=
    evalExpr (ITE (Var type Bool (dGe rem den))
                  (Sub (Var type (Bit (f + 2)) rem) (Var type (Bit (f + 2)) (dDenx den)))
                  (Var type (Bit (f + 2)) rem)).
  Definition dRemNext (rem : bits (f + 2)) (den : bits (f + 1)) : bits (f + 2) :=
    evalExpr (Sll (Var type (Bit (f + 2)) (dRem1 rem den)) (@cst type (f + 2) 1)).
  Definition dQuotNext (rem : bits (f + 2)) (den : bits (f + 1)) (quot : bits (f + 3)) : bits (f + 3) :=
    evalExpr (Or [ Sll (Var type (Bit (f + 3)) quot) (@cst type (f + 3) 1) ;
                   ITE (Var type Bool (dGe rem den)) (@cst type (f + 3) 1) (@cst type (f + 3) 0) ]).

  Lemma divStep_eval : forall info rem den quot,
    evalLetExpr (step type (info ,, (rem ,, (den ,, (quot ,, tt))))) =
    (info ,, (dRemNext rem den ,, (den ,, (dQuotNext rem den quot ,, tt)))).
  Proof. intros; timeout 20 reflexivity. Qed.

  Lemma divInit_eval : forall req,
    let info := evalLetExpr (divInfoOf true e f xlen type req) in
    evalLetExpr (init type req) =
    (info ,, (evalExpr (zext (f + 1) (f + 2) (Var type (Bit (f + 1)) (info @% "ua" @% "sig"))) ,,
             (info @% "ub" @% "sig" ,, (evalExpr (@cst type (f + 3) 0) ,, tt)))).
  Proof. intros req info; timeout 20 reflexivity. Qed.

  Lemma divInfo_ub : forall req,
    (evalLetExpr (divInfoOf true e f xlen type req)) @% "ub" = evalLetExpr (fpUnpack true e f type (req @% "b")).
  Proof. intros req; timeout 20 reflexivity. Qed.

  Lemma divFinish_eval : forall info rem den quot,
    evalLetExpr (finish type (info ,, (rem ,, (den ,, (quot ,, tt))))) =
    evalLetExpr (divFinishCore true e f type info quot (evalExpr (isNotZero (Var type (Bit (f + 2)) rem)))).
  Proof.
    intros; unfold divFinish; cbn [evalLetExpr].
    apply f_equal; apply (f_equal3 (divFinishCore true e f type)); timeout 20 reflexivity.
  Qed.

  Lemma divSpec_eval : forall req,
    let info := evalLetExpr (divInfoOf true e f xlen type req) in
    let nn := evalExpr (divNumer f type (info @% "ua" @% "sig")) in
    let dd := evalExpr (divDenom f type (info @% "ub" @% "sig")) in
    evalLetExpr (divSpec true e f xlen type req) =
    evalLetExpr (divFinishCore true e f type info
      (evalExpr (trunc (2 * f + 3) (f + 3) (Div (Var type (Bit (2 * f + 3)) nn) (Var type (Bit (2 * f + 3)) dd))))
      (evalExpr (isNotZero (Rem (Var type (Bit (2 * f + 3)) nn) (Var type (Bit (2 * f + 3)) dd))))).
  Proof.
    intros req info nn dd; unfold divSpec; cbn [evalLetExpr].
    apply f_equal; apply (f_equal3 (divFinishCore true e f type)); timeout 20 reflexivity.
  Qed.

  Lemma unsigned_cst_small : forall w v, 0 <= v < 2 ^ w -> 0 <= w ->
    Zmod.unsigned (evalExpr (@cst type w v)) = v.
  Proof. intros w v Hv Hw; rewrite unsigned_cst by lia; apply Z.mod_small; lia. Qed.

  Lemma divStep_arith : forall (rem : bits (f + 2)) (den : bits (f + 1)) (quot : bits (f + 3)),
    let R := Zmod.unsigned rem in
    let B := Zmod.unsigned den in
    let Q := Zmod.unsigned quot in
    R < 2 * B -> Q < 2 ^ (f + 2) ->
    Zmod.unsigned (dRemNext rem den) = 2 * (if R <? B then R else R - B) /\
    Zmod.unsigned (dQuotNext rem den quot) = 2 * Q + (if R <? B then 0 else 1).
  Proof.
    intros rem den quot R B Q HR HQ.
    pose proof (bits_unsigned_bound (f + 1) den ltac:(lia)) as HB; fold B in HB.
    pose proof (bits_unsigned_bound (f + 2) rem ltac:(lia)) as HRr; fold R in HRr.
    pose proof (bits_unsigned_bound (f + 3) quot ltac:(lia)) as HQr; fold Q in HQr.
    assert (Hdenx : Zmod.unsigned (dDenx den) = B).
    { unfold dDenx; rewrite unsigned_zext by lia; reflexivity. }
    assert (Hge : dGe rem den = negb (R <? B)).
    { unfold dGe; cbn [evalExpr evalNot].
      change (Zmod.to_Z rem) with R.
      change (Zmod.to_Z (dDenx den)) with (Zmod.unsigned (dDenx den)).
      rewrite Hdenx; reflexivity. }
    assert (H2B : 2 * B <= 2 ^ (f + 2)).
    { replace (f + 2) with ((f + 1) + 1) by lia; rewrite Z.pow_add_r by lia; lia. }
    assert (Hone2 : Zmod.to_Z (evalExpr (@cst type (f + 2) 1)) = 1).
    { change (Zmod.to_Z (evalExpr (@cst type (f + 2) 1))) with (Zmod.unsigned (evalExpr (@cst type (f + 2) 1))).
      apply unsigned_cst_small; [split; [lia |] | lia].
      replace (f + 2) with (1 + (f + 1)) by lia; rewrite Z.pow_add_r by lia.
      pose proof (Z.pow_pos_nonneg 2 (f + 1) ltac:(lia) ltac:(lia)); lia. }
    assert (Hone3 : Zmod.to_Z (evalExpr (@cst type (f + 3) 1)) = 1).
    { change (Zmod.to_Z (evalExpr (@cst type (f + 3) 1))) with (Zmod.unsigned (evalExpr (@cst type (f + 3) 1))).
      apply unsigned_cst_small; [split; [lia |] | lia].
      replace (f + 3) with (1 + (f + 2)) by lia; rewrite Z.pow_add_r by lia.
      pose proof (Z.pow_pos_nonneg 2 (f + 2) ltac:(lia) ltac:(lia)); lia. }
    assert (H2Q : 2 * Q + 1 < 2 ^ (f + 3)).
    { replace (f + 3) with ((f + 2) + 1) by lia; rewrite Z.pow_add_r by lia; lia. }
    unfold dRemNext, dQuotNext, dRem1.
    rewrite Hge.
    destruct (R <? B) eqn:HRB; cbn [negb].
    - apply Z.ltb_lt in HRB.
      cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
      rewrite Hone2, Hone3.
      rewrite !bits.unsigned_or, Zmod.unsigned_0, !Z.lor_0_l.
      rewrite !Zmod.unsigned_slu, !Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2.
      change (Zmod.unsigned rem) with R; change (Zmod.unsigned quot) with Q.
      rewrite (unsigned_cst_small (f + 3) 0) by (pose proof (Z.pow_pos_nonneg 2 (f + 3) ltac:(lia) ltac:(lia)); lia).
      rewrite Z.lor_0_r.
      split; rewrite Z.mod_small by lia; lia.
    - apply Z.ltb_ge in HRB.
      cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
      rewrite Hone2, Hone3.
      rewrite !bits.unsigned_or, Zmod.unsigned_0, !Z.lor_0_l.
      rewrite !Zmod.unsigned_slu, !Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2.
      rewrite (unsigned_sub_ge (f + 2) rem (dDenx den)) by lia.
      rewrite Hdenx.
      change (Zmod.unsigned rem) with R; change (Zmod.unsigned quot) with Q.
      rewrite (unsigned_cst_small (f + 3) 1) by lia.
      rewrite (Z.mod_small (Q * 2)) by lia.
      replace (Q * 2) with (2 * Q) by ring.
      rewrite lor_mul2_bit by lia.
      split; [rewrite Z.mod_small by lia; lia | lia].
  Qed.

  Lemma StageValAt_div : forall (k : nat) req,
    Z.of_nat k <= f + 3 ->
    let info := evalLetExpr (divInfoOf true e f xlen type req) in
    let A := Zmod.unsigned (info @% "ua" @% "sig") in
    let B := Zmod.unsigned (info @% "ub" @% "sig") in
    exists (rem : bits (f + 2)) (quot : bits (f + 3)),
      StageValAt init step k req = (info ,, (rem ,, (info @% "ub" @% "sig" ,, (quot ,, tt)))) /\
      A * 2 ^ Z.of_nat k = 2 * Zmod.unsigned quot * B + Zmod.unsigned rem /\
      Zmod.unsigned rem < 2 * B /\
      Zmod.unsigned quot < 2 ^ Z.of_nat k /\
      (k = 0%nat \/ Z.even (Zmod.unsigned rem) = true).
  Proof.
    intros k req Hk info A B.
    pose proof (bits_unsigned_bound (f + 1) (info @% "ua" @% "sig") ltac:(lia)) as HA; fold A in HA.
    assert (HBge : 2 ^ f <= B).
    { unfold B, info; rewrite divInfo_ub; apply fpUnpack_sig_ge; lia. }
    assert (H2B : 2 ^ (f + 1) <= 2 * B) by (rewrite Z.pow_add_r by lia; lia).
    induction k as [| k IH].
    - exists (evalExpr (zext (f + 1) (f + 2) (Var type (Bit (f + 1)) (info @% "ua" @% "sig")))),
             (evalExpr (@cst type (f + 3) 0)).
      cbn [StageValAt]; rewrite divInit_eval; fold info.
      rewrite unsigned_zext, evalExpr_Var by lia; fold A.
      rewrite (unsigned_cst_small (f + 3) 0) by (pose proof (Z.pow_pos_nonneg 2 (f + 3) ltac:(lia) ltac:(lia)); lia).
      change (2 ^ Z.of_nat 0) with 1.
      split; [reflexivity |]; split; [lia |]; split; [lia |]; split; [lia | left; reflexivity].
    - destruct IH as [rem [quot [Heq [Hinv [HR [HQ _]]]]]]; [lia |].
      set (sigb := info @% "ub" @% "sig") in *.
      pose proof (divStep_arith rem sigb quot) as Harith; cbv zeta in Harith; fold B in Harith.
      assert (HQ2 : Zmod.unsigned quot < 2 ^ (f + 2)).
      { eapply Z.lt_le_trans; [exact HQ | apply Z.pow_le_mono_r; lia]. }
      destruct (Harith HR HQ2) as [Hrem' Hquot'].
      exists (dRemNext rem sigb), (dQuotNext rem sigb quot).
      cbn [StageValAt]; rewrite Heq, divStep_eval.
      split; [reflexivity |].
      rewrite Hrem', Hquot'.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2.
      destruct (Zmod.unsigned rem <? B) eqn:HRB;
        [apply Z.ltb_lt in HRB | apply Z.ltb_ge in HRB].
      + split; [nia |]; split; [lia |]; split; [lia |].
        right; rewrite Z.even_mul; reflexivity.
      + split; [nia |]; split; [lia |]; split; [lia |].
        right; rewrite Z.even_mul; reflexivity.
  Qed.

  Theorem Div_StageValAt_spec : forall req,
    evalLetExpr (finish type (StageValAt init step (divSteps f) req)) =
    evalLetExpr (divSpec true e f xlen type req).
  Proof.
    intros req.
    assert (Hk : Z.of_nat (divSteps f) = f + 3) by (unfold divSteps; lia).
    destruct (StageValAt_div (divSteps f) req ltac:(lia)) as [rem [quot [Heq [Hinv [HR [HQ Hev]]]]]].
    set (info := evalLetExpr (divInfoOf true e f xlen type req)) in *.
    set (A := Zmod.unsigned (info @% "ua" @% "sig")) in *.
    set (B := Zmod.unsigned (info @% "ub" @% "sig")) in *.
    rewrite Hk in Hinv, HQ.
    rewrite Heq, divFinish_eval, divSpec_eval; fold info.
    pose proof (bits_unsigned_bound (f + 1) (info @% "ua" @% "sig") ltac:(lia)) as HA; fold A in HA.
    assert (HBge : 2 ^ f <= B).
    { unfold B, info; rewrite divInfo_ub; apply fpUnpack_sig_ge; lia. }
    assert (HBpos : 0 < B) by (pose proof (Z.pow_pos_nonneg 2 f ltac:(lia) ltac:(lia)); lia).
    destruct Hev as [Habs | Hev]; [unfold divSteps in Habs; lia |].
    apply Z.even_spec in Hev; destruct Hev as [r1 Hrem2].
    (* siga * 2^(f+2) = quot * sigb + r1 with 0 <= r1 < sigb *)
    assert (Hp3 : 2 ^ (f + 3) = 2 * 2 ^ (f + 2)) by (replace (f + 3) with ((f + 2) + 1) by lia; rewrite Z.pow_add_r by lia; lia).
    pose proof (bits_unsigned_bound (f + 2) rem ltac:(lia)) as Hremr.
    assert (Hdivmod : A * 2 ^ (f + 2) = Zmod.unsigned quot * B + r1) by nia.
    assert (Hr1 : 0 <= r1 < B) by lia.
    assert (Hq : A * 2 ^ (f + 2) / B = Zmod.unsigned quot).
    { symmetry; apply (Z.div_unique _ _ _ r1); [lia | lia]. }
    assert (Hm : A * 2 ^ (f + 2) mod B = r1).
    { symmetry; apply (Z.mod_unique _ _ (Zmod.unsigned quot)); [lia | lia]. }
    assert (Hnn : Zmod.unsigned (evalExpr (divNumer f type (info @% "ua" @% "sig"))) = A * 2 ^ (f + 2)).
    { assert (Hsh : Zmod.to_Z (evalExpr (@cst type (2 * f + 3) (f + 2))) = f + 2).
      { change (Zmod.to_Z (evalExpr (@cst type (2 * f + 3) (f + 2))))
          with (Zmod.unsigned (evalExpr (@cst type (2 * f + 3) (f + 2)))).
        apply unsigned_cst_small; [| lia].
        split; [lia |].
        apply Z.lt_le_trans with (2 ^ (f + 2)); [apply Z.pow_gt_lin_r; lia | apply Z.pow_le_mono_r; lia]. }
      unfold divNumer; cbn [evalExpr].
      rewrite Zmod.unsigned_slu, Hsh, Z.shiftl_mul_pow2 by lia.
      rewrite unsigned_zext, evalExpr_Var by lia; fold A.
      pose proof (Z.pow_pos_nonneg 2 (f + 2) ltac:(lia) ltac:(lia)) as Hp2.
      apply Z.mod_small; split; [nia |].
      replace (2 * f + 3) with ((f + 1) + (f + 2)) by lia.
      rewrite (Z.pow_add_r 2 (f + 1) (f + 2)) by lia; nia. }
    assert (Hdd : Zmod.unsigned (evalExpr (divDenom f type (info @% "ub" @% "sig"))) = B).
    { unfold divDenom; rewrite unsigned_zext, evalExpr_Var by lia; reflexivity. }
    apply f_equal; apply (f_equal3 (divFinishCore true e f type)); [reflexivity | |].
    - apply Zmod.unsigned_inj.
      rewrite unsigned_trunc by lia.
      cbn [evalExpr].
      rewrite Zmod.unsigned_udiv_nonneg; [| apply Z.pow_nonneg; lia | rewrite Hdd; lia].
      rewrite Hnn, Hdd, Hq.
      pose proof (bits_unsigned_bound (f + 3) quot ltac:(lia)).
      symmetry; apply Z.mod_small; split; [lia | exact HQ].
    - rewrite !evalExpr_isNotZero_bits.
      cbn [evalExpr].
      rewrite Zmod.unsigned_umod, Hnn, Hdd, Hm, Hrem2.
      destruct (Z.eqb_spec r1 0) as [H0 | H0]; [rewrite H0; reflexivity |].
      destruct (Z.eqb_spec (2 * r1) 0); [lia | reflexivity].
  Qed.
End DivProof.

(* ===========================================================================
 * 5. THE SINGLE-FORMAT COMPUTE FUNCTION DISPATCHES TO THE THREE UNITS
 * =========================================================================== *)

Lemma fpuCompute_dispatch : forall (e f xlen wlen : Z) (req : type (FpReqK e f xlen)),
  evalLetExpr (fpuCompute true e f xlen wlen type req) =
  if req @% "op" @% "div"
  then evalExpr (fpRes e f xlen type (evalLetExpr (divSpec true e f xlen type req)))
  else if req @% "op" @% "sqrt"
  then evalExpr (fpRes e f xlen type (evalLetExpr (sqrtSpec true e f xlen type req)))
  else evalLetExpr (pipeSpec true e f xlen wlen type req).
Proof. intros; exact eq_refl. Qed.

(* ===========================================================================
 * 6. CONTROLLER THEOREMS FOR THE THREE UNITS
 * =========================================================================== *)

Lemma iterStepsSz_unsigned_nat : forall (k n : nat),
  (k <= n)%nat ->
  Z.to_nat (Zmod.unsigned (bits.of_Z (iterStepsSz n) (Z.of_nat k))) = k.
Proof.
  intros k n Hle.
  assert (Hpow : Z.of_nat k < 2 ^ iterStepsSz n).
  { unfold iterStepsSz.
    destruct (Z.eq_dec (Z.of_nat n + 1) 1) as [Heq1 | Hne1].
    - assert (k = 0)%nat by lia; subst k; cbn; lia.
    - assert (Hgt1 : 1 < Z.of_nat n + 1) by lia.
      pose proof (proj2 (Z.log2_up_spec (Z.of_nat n + 1) Hgt1)) as Hup.
      assert (Hle_max : Z.log2_up (Z.of_nat n + 1) <= Z.max 1 (Z.log2_up (Z.of_nat n + 1))) by lia.
      pose proof (Z.pow_le_mono_r 2 (Z.log2_up (Z.of_nat n + 1)) (Z.max 1 (Z.log2_up (Z.of_nat n + 1))) ltac:(lia) Hle_max).
      lia. }
  replace (Zmod.unsigned (bits.of_Z (iterStepsSz n) (Z.of_nat k))) with (Z.of_nat k)
    by (symmetry; unfold bits.of_Z; apply Zmod.unsigned_of_Z_small; lia).
  apply Nat2Z.id.
Qed.

Section PipeUnitInvariants.
  Variable e f xlen wlen : Z.
  Variable mul_stages mul_bps : nat.

  Local Abbreviation mw := (mul_stages * mul_bps)%nat.
  Local Abbreviation SK := (PipeStateK e f xlen mw).
  Local Abbreviation IK := (FpReqK e f xlen).
  Local Abbreviation init := (pipeInit e f xlen mul_stages mul_bps).
  Local Abbreviation step := (pipeStep e f xlen mul_stages mul_bps).
  Local Abbreviation finish := (pipeFinish e f xlen wlen mul_stages mul_bps).

  Definition FpPipe_StageAtStep (inp : type IK) (k : nat) (fs : TreeState ElemState (fifoTree 1 SK)) : Prop :=
    PipeStageAtStep IK SK init step inp k fs.

  Theorem FpPipe_Enq_Stage0 :
    forall {env : Env (fpPipeTree e f xlen mul_stages mul_bps)} (inp : type IK)
           (s s' : TreeState ElemState (fpPipeTree e f xlen mul_stages mul_bps)) ret,
      fifo1_size (s.(Fst)) = Zmod.of_Z 2 0 ->
      SemAction env (fpPipeEnq e f xlen mul_stages mul_bps type inp) s s' ret ->
      FpPipe_StageAtStep inp 0%nat (s'.(Fst)).
  Proof.
    intros env inp s s' ret Hemp Hsem.
    exact (Pipe_Enq_Stage0 IK SK mul_stages init step inp s s' ret Hemp Hsem).
  Qed.

  Theorem FpPipe_Step_Adjacent_Inductive :
    forall (inp : type IK) (k m : nat) {env : Env (stagedStagesTree SK (S m))}
           (st st' : TreeState ElemState (stagedStagesTree SK (S m))) ret,
      FpPipe_StageAtStep inp k (st.(Fst)) ->
      fifo1_size (st.(Snd).(Fst).(Fst)) = Zmod.of_Z 2 0 ->
      SemAction env (stagedPipeStepAdjacent SK step type m) st st' ret ->
      fifo1_size (st'.(Fst)) = Zmod.of_Z 2 0 /\
      FpPipe_StageAtStep inp (S k) (st'.(Snd).(Fst).(Fst)).
  Proof.
    intros inp k m env st st' ret Hcur Hnext Hsem.
    exact (Pipe_Step_Adjacent_Inductive IK SK init step inp k m st st' ret Hcur Hnext Hsem).
  Qed.

  Theorem FpPipe_First_Spec :
    forall {env : Env (fpPipeTree e f xlen mul_stages mul_bps)} (inp : type IK)
           (s s' : TreeState ElemState (fpPipeTree e f xlen mul_stages mul_bps)) optOut,
      (0 < mw)%nat -> 0 <= f -> f + 1 <= dataLen mw ->
      FpPipe_StageAtStep inp mul_stages (stagedLastFifo SK mul_stages s) ->
      SemAction env (fpPipeFirst e f xlen wlen mul_stages mul_bps type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type (FpResK e f xlen) (evalLetExpr (pipeSpec true e f xlen wlen type inp)))).
  Proof.
    intros env inp s s' optOut Hmw Hf Hfit Hstage Hsem.
    exact (Pipe_First_Spec IK SK (FpResK e f xlen) mul_stages init step finish (pipeSpec true e f xlen wlen)
             inp s s' optOut (Pipe_StageValAt_spec e f xlen wlen mul_stages mul_bps Hmw Hf Hfit inp) Hstage Hsem).
  Qed.

  Theorem FpPipe_Deq_LastStage :
    forall {env : Env (fpPipeTree e f xlen mul_stages mul_bps)}
           (s s' : TreeState ElemState (fpPipeTree e f xlen mul_stages mul_bps)) ret,
      fifo1_size (stagedLastFifo SK mul_stages s) = Zmod.of_Z 2 1 ->
      SemAction env (fpPipeDeq e f xlen mul_stages mul_bps type) s s' ret ->
      fifo1_size (stagedLastFifo SK mul_stages s') = Zmod.of_Z 2 0.
  Proof.
    intros env s s' ret Hfull Hsem.
    exact (Pipe_Deq_LastStage SK mul_stages s s' ret Hfull Hsem).
  Qed.
End PipeUnitInvariants.

Section DivUnitInvariants.
  Variable e f xlen wlen : Z.

  Local Abbreviation SK := (DivStateK e f).
  Local Abbreviation IK := (FpReqK e f xlen).
  Local Abbreviation n := (divSteps f).
  Local Abbreviation nfn := (divStepsConst e f xlen).
  Local Abbreviation init := (divInit e f xlen).
  Local Abbreviation step := (divStep e f).
  Local Abbreviation finish := (divFinish e f).

  Lemma IterTargetSteps_div : forall inp, IterTargetSteps IK n nfn inp = n.
  Proof.
    intros inp; unfold IterTargetSteps, divStepsConst; cbn -[iterStepsSz bits.of_Z].
    apply iterStepsSz_unsigned_nat; lia.
  Qed.

  Definition FpDiv_StateAtStep (inp : type IK) (m : nat) (s : TreeState ElemState (fpDivTree e f)) : Prop :=
    IterStateAtStep IK SK n nfn init step inp m s.

  Theorem FpDiv_Enq_Step0 :
    forall {env : Env (fpDivTree e f)} (inp : type IK) (s s' : TreeState ElemState (fpDivTree e f)) ret,
      s @% "busy" = false ->
      SemAction env (fpDivEnq e f xlen type inp) s s' ret ->
      FpDiv_StateAtStep inp 0%nat s'.
  Proof.
    intros env inp s s' ret Hidle Hsem.
    exact (Iter_Enq_Step0 IK SK n nfn init step inp s s' ret Hidle Hsem).
  Qed.

  Theorem FpDiv_Step_Inductive :
    forall {env : Env (fpDivTree e f)} (inp : type IK) (m : nat) (s s' : TreeState ElemState (fpDivTree e f)) ret,
      FpDiv_StateAtStep inp m s ->
      (m < n)%nat ->
      SemAction env (fpDivStepRule e f type) s s' ret ->
      FpDiv_StateAtStep inp (S m) s'.
  Proof.
    intros env inp m s s' ret Hst Hlt Hsem.
    eapply (Iter_Step_Inductive IK SK n nfn init step inp m s s' ret Hst); [| exact Hsem].
    rewrite IterTargetSteps_div; exact Hlt.
  Qed.

  Theorem FpDiv_First_Spec :
    forall {env : Env (fpDivTree e f)} (inp : type IK) (s s' : TreeState ElemState (fpDivTree e f)) optOut,
      0 <= f ->
      FpDiv_StateAtStep inp n s ->
      SemAction env (fpDivFirst e f type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type (FpOutK e f) (evalLetExpr (divSpec true e f xlen type inp)))).
  Proof.
    intros env inp s s' optOut Hf Hst Hsem.
    eapply (Iter_First_Spec IK SK (FpOutK e f) n nfn init step finish (divSpec true e f xlen) inp s s' optOut);
      [| | exact Hsem].
    - rewrite IterTargetSteps_div; apply (Div_StageValAt_spec e f xlen Hf).
    - unfold FpDiv_StateAtStep in Hst; rewrite IterTargetSteps_div; exact Hst.
  Qed.

  Theorem FpDiv_Deq_Idle :
    forall {env : Env (fpDivTree e f)} (inp : type IK) (s s' : TreeState ElemState (fpDivTree e f)) ret,
      FpDiv_StateAtStep inp n s ->
      SemAction env (fpDivDeq e f type) s s' ret ->
      s' @% "busy" = false.
  Proof.
    intros env inp s s' ret Hst Hsem.
    eapply (Iter_Deq_Idle IK SK n nfn init step inp s s' ret); [| exact Hsem].
    unfold FpDiv_StateAtStep in Hst; rewrite IterTargetSteps_div; exact Hst.
  Qed.
End DivUnitInvariants.

Section SqrtUnitInvariants.
  Variable e f xlen wlen : Z.

  Local Abbreviation SK := (SqrtStateK e f).
  Local Abbreviation IK := (FpReqK e f xlen).
  Local Abbreviation n := (sqrtSteps f).
  Local Abbreviation nfn := (sqrtStepsConst e f xlen).
  Local Abbreviation init := (sqrtInit true e f xlen).
  Local Abbreviation step := (sqrtStep e f).
  Local Abbreviation finish := (sqrtFinish true e f).

  Lemma IterTargetSteps_sqrt : forall inp, IterTargetSteps IK n nfn inp = n.
  Proof.
    intros inp; unfold IterTargetSteps, sqrtStepsConst; cbn -[iterStepsSz bits.of_Z sqrtSteps].
    apply iterStepsSz_unsigned_nat; lia.
  Qed.

  Definition FpSqrt_StateAtStep (inp : type IK) (m : nat) (s : TreeState ElemState (fpSqrtTree e f)) : Prop :=
    IterStateAtStep IK SK n nfn init step inp m s.

  Theorem FpSqrt_Enq_Step0 :
    forall {env : Env (fpSqrtTree e f)} (inp : type IK) (s s' : TreeState ElemState (fpSqrtTree e f)) ret,
      s @% "busy" = false ->
      SemAction env (fpSqrtEnq e f xlen type inp) s s' ret ->
      FpSqrt_StateAtStep inp 0%nat s'.
  Proof.
    intros env inp s s' ret Hidle Hsem.
    exact (Iter_Enq_Step0 IK SK n nfn init step inp s s' ret Hidle Hsem).
  Qed.

  Theorem FpSqrt_Step_Inductive :
    forall {env : Env (fpSqrtTree e f)} (inp : type IK) (m : nat) (s s' : TreeState ElemState (fpSqrtTree e f)) ret,
      FpSqrt_StateAtStep inp m s ->
      (m < n)%nat ->
      SemAction env (fpSqrtStepRule e f type) s s' ret ->
      FpSqrt_StateAtStep inp (S m) s'.
  Proof.
    intros env inp m s s' ret Hst Hlt Hsem.
    eapply (Iter_Step_Inductive IK SK n nfn init step inp m s s' ret Hst); [| exact Hsem].
    rewrite IterTargetSteps_sqrt; exact Hlt.
  Qed.

  Theorem FpSqrt_First_Spec :
    forall {env : Env (fpSqrtTree e f)} (inp : type IK) (s s' : TreeState ElemState (fpSqrtTree e f)) optOut,
      FpSqrt_StateAtStep inp n s ->
      SemAction env (fpSqrtFirst e f type) s s' optOut ->
      s' = s /\
      optOut = evalExpr (mkSome (Const type (FpOutK e f) (evalLetExpr (sqrtSpec true e f xlen type inp)))).
  Proof.
    intros env inp s s' optOut Hst Hsem.
    eapply (Iter_First_Spec IK SK (FpOutK e f) n nfn init step finish (sqrtSpec true e f xlen) inp s s' optOut);
      [| | exact Hsem].
    - rewrite IterTargetSteps_sqrt; apply Sqrt_StageValAt_spec.
    - unfold FpSqrt_StateAtStep in Hst; rewrite IterTargetSteps_sqrt; exact Hst.
  Qed.

  Theorem FpSqrt_Deq_Idle :
    forall {env : Env (fpSqrtTree e f)} (inp : type IK) (s s' : TreeState ElemState (fpSqrtTree e f)) ret,
      FpSqrt_StateAtStep inp n s ->
      SemAction env (fpSqrtDeq e f type) s s' ret ->
      s' @% "busy" = false.
  Proof.
    intros env inp s s' ret Hst Hsem.
    eapply (Iter_Deq_Idle IK SK n nfn init step inp s s' ret); [| exact Hsem].
    unfold FpSqrt_StateAtStep in Hst; rewrite IterTargetSteps_sqrt; exact Hst.
  Qed.
End SqrtUnitInvariants.
