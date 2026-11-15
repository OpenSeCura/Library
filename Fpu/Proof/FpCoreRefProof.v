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
 * The biased hardware model equals the unbiased reference model (`FpCoreRefProof.v`).
 *
 * `FpCore.v` is generic in the exponent mode `bm`: `bm = true` keeps exponents biased (the spec and
 * the units use it), `bm = false` is the readable reference (`FpCoreRef.v`).  Their internal
 * exponents differ by the bias `B` (`shiftV`), and every exponent-dependent decision is the same
 * as long as no internal exponent wraps around in `e + 3` bits (`InRange`).
 *
 * Structure: (a) unpacking shifts the exponent (`fpUnpack_shift`); (b) rounding is unchanged by
 * the shift (`rpExp_eq`, `roundPack_eq`, `normRound_eq`); (c) every operation (`*_eq`), with
 * range lemmas for its internal exponents; (d) the whole compute function
 * (`fpuCompute_ref_equiv`) and the format conversion (`cvtFF_ref_equiv`).
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift FpuUnitsProof.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section Equiv.
  Variable e f xlen : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.

  Local Abbreviation W := (e + 3).
  Local Abbreviation B := (fpBias e).
  Local Abbreviation sh := (shiftV W B).
  Local Abbreviation IR := (InRange W B).

  Add Ring zringW : (Zmod.ring_theory (2 ^ W)).

  Lemma W_pos : 1 <= W. Proof. lia. Qed.

  Lemma B_range : 0 <= B < 2 ^ (W - 1).
  Proof.
    unfold fpBias; assert (2 ^ (e - 1) < 2 ^ (e + 2)) by (apply Z.pow_lt_mono_r; lia).
    assert (2 ^ 0 <= 2 ^ (e - 1)) by (apply Z.pow_le_mono_r; lia).
    replace (e + 3 - 1) with (e + 2) by lia; lia.
  Qed.

  Local Ltac shtac := pose proof W_pos; pose proof B_range.

  (* ---------------------------------------------------------------------------
   * (b) ROUNDING
   * --------------------------------------------------------------------------- *)

  (* The value of `rpExp`, with every constant written as `k + expOff`. *)
  Definition rpExpV (bm : bool) (x : bits W) : type (RpExpK e) :=
    let emin := Zmod.of_Z (2 ^ W) (fpEmin e + expOff bm e) in
    let tp := Z.ltb (Zmod.signed x) (Zmod.signed emin) in
    let dRaw := Zmod.sub emin x in
    let shv := if tp then (if Z.ltb (Zmod.unsigned dRaw) (Zmod.unsigned (Zmod.of_Z (2 ^ W) (f + 3)))
                           then dRaw else Zmod.of_Z (2 ^ W) (f + 3))
               else Zmod.of_Z (2 ^ W) 0 in
    let xEff := if tp then emin else x in
    let bm1 := Zmod.add (Zmod.add Zmod.zero xEff) (Zmod.of_Z (2 ^ W) (fpBias e - 1 - expOff bm e)) in
    (tp ,, (shv ,, (bm1 ,,
     (evalExpr (Slt (cst W (fpEmax e + expOff bm e)) (Var type (Bit W) x)) ,,
     (Zmod.eqb x (Zmod.of_Z (2 ^ W) (fpEmin e - 1 + expOff bm e)) ,, tt))))).

  Lemma rpExp_eval : forall bm x, evalLetExpr (rpExp bm e f type x) = rpExpV bm x.
  Proof.
    intros bm x; unfold rpExp; cbn [evalLetExpr].
    rewrite !slt_eval by (exact W_pos); rewrite !(sub_eval W ltac:(lia)); exact eq_refl.
  Qed.

  Lemma IR_emin : IR (Zmod.of_Z _ (fpEmin e)).
  Proof.
    shtac; apply InRange_of_Z; unfold fpEmin, fpBias in *;
      assert (2 ^ (e - 1) < 2 ^ (e + 2)) by (apply Z.pow_lt_mono_r; lia);
      replace (e + 3 - 1) with (e + 2) in * by lia; lia.
  Qed.

  Lemma IR_emax : IR (Zmod.of_Z _ (fpEmax e)).
  Proof.
    shtac; apply InRange_of_Z; unfold fpEmax, fpBias in *;
      assert (2 * 2 ^ (e - 1) <= 2 ^ (e + 2)) by
        (rewrite <- Z.pow_succ_r by lia; apply Z.pow_le_mono_r; lia);
      replace (e + 3 - 1) with (e + 2) in * by lia; lia.
  Qed.

  Lemma IR_eminm1 : IR (Zmod.of_Z _ (fpEmin e - 1)).
  Proof.
    shtac; apply InRange_of_Z; unfold fpEmin, fpBias in *;
      assert (2 ^ (e - 1) < 2 ^ (e + 2)) by (apply Z.pow_lt_mono_r; lia);
      replace (e + 3 - 1) with (e + 2) in * by lia; lia.
  Qed.

  Lemma bm1_shift : forall y : bits W,
    Zmod.add (Zmod.add Zmod.zero (sh y)) (Zmod.of_Z _ (B - 1 - B)) = Zmod.add (Zmod.add Zmod.zero y) (Zmod.of_Z _ (B - 1)).
  Proof.
    intros y; replace (B - 1 - B) with (-1) by lia; replace (B - 1) with (B + -1) by lia.
    rewrite Zmod.of_Z_add; unfold shiftV; ring.
  Qed.

  Lemma rpExp_eq : forall x, IR x -> evalLetExpr (rpExp true e f type (sh x)) = evalLetExpr (rpExp false e f type x).
  Proof.
    intros x Hx; shtac; rewrite !rpExp_eval; unfold rpExpV; rewrite !slt_eval by (exact W_pos).
    cbn [evalExpr cst]; unfold expOff; cbv zeta.
    rewrite <- !(shift_of_Z W B), !Z.add_0_r, !Z.sub_0_r.
    rewrite (slt_shift W W_pos B B_range x _ Hx IR_emin).
    rewrite (slt_shift W W_pos B B_range _ x IR_emax Hx).
    rewrite (shift_eqb W B).
    rewrite (shift_sub W B).
    destruct (Z.ltb (Zmod.signed x) (Zmod.signed (Zmod.of_Z (2 ^ W) (fpEmin e)))); rewrite bm1_shift; exact eq_refl.
  Qed.

  Lemma roundPack_eq : forall s x sigR st rm, IR x ->
    evalLetExpr (roundPack true e f type s (sh x) sigR st rm) = evalLetExpr (roundPack false e f type s x sigR st rm).
  Proof.
    intros s x sigR st rm Hx; unfold roundPack; cbn [evalLetExpr]; rewrite (rpExp_eq x Hx); exact eq_refl.
  Qed.

  Lemma normRound_eq : forall Wd s x wsig st rm, 0 <= Wd ->
    (forall k, 0 <= k <= Wd -> IR (Zmod.sub x (Zmod.of_Z _ k))) ->
    evalLetExpr (normRound true e f type Wd s (sh x) wsig st rm) = evalLetExpr (normRound false e f type Wd s x wsig st rm).
  Proof.
    intros Wd s x wsig st rm HW Hr.
    destruct (clz_val Wd (e + 3) wsig HW) as [k [Hk Hc]].
    unfold normRound; cbn [evalLetExpr]. rewrite !Hc. rewrite !(sub_eval W ltac:(lia)).
    assert (E : Zmod.sub (evalExpr (Var type (Bit W) (sh x))) (evalExpr (Var type (Bit W) (Zmod.of_Z (2 ^ W) k)))
                = sh (Zmod.sub x (Zmod.of_Z _ k))) by exact (shift_sub_r W B x _).
    rewrite E.
    rewrite (roundPack_eq _ _ _ _ _ (Hr k Hk)). exact eq_refl.
  Qed.

  (* The same, when the window is already normalized (no leading zeros). *)
  Lemma normRound_eq0 : forall Wd s x wsig st rm, evalExpr (clz Wd W wsig) = Zmod.of_Z _ 0 -> IR x ->
    evalLetExpr (normRound true e f type Wd s (sh x) wsig st rm) = evalLetExpr (normRound false e f type Wd s x wsig st rm).
  Proof.
    intros Wd s x wsig st rm Hc Hx.
    unfold normRound; cbn [evalLetExpr]. rewrite !Hc. rewrite !(sub_eval W ltac:(lia)).
    assert (E : Zmod.sub (evalExpr (Var type (Bit W) (sh x))) (evalExpr (Var type (Bit W) (Zmod.of_Z (2 ^ W) 0)))
                = sh (Zmod.sub x (Zmod.of_Z _ 0))) by exact (shift_sub_r W B x _).
    rewrite E.
    assert (Hx0 : IR (Zmod.sub x (Zmod.of_Z (2 ^ W) 0))) by (rewrite Zmod.of_Z_0, Zmod.sub_0_r; exact Hx).
    rewrite (roundPack_eq _ _ _ _ _ Hx0). exact eq_refl.
  Qed.

  (* ---------------------------------------------------------------------------
   * (a) UNPACK
   * --------------------------------------------------------------------------- *)

  (* The unpacked record with its exponent shifted. *)
  Definition ukS (u : type (FpUnpK e f)) : type (FpUnpK e f) :=
    (u.(Fst) ,, (u.(Snd).(Fst) ,, (u.(Snd).(Snd).(Fst) ,, (u.(Snd).(Snd).(Snd).(Fst) ,,
    (u.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (sh u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (u.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt))))))).

  Lemma fpUnpack_shift : forall a, evalLetExpr (fpUnpack true e f type a) = ukS (evalLetExpr (fpUnpack false e f type a)).
  Proof.
    intros a; unfold fpUnpack, expUnpack; cbn [evalLetExpr]; rewrite !(sub_eval W ltac:(lia)).
    match goal with |- context [Zmod.sub (Zmod.sub ?eb ?c) ?lz] =>
      assert (E : Zmod.sub eb lz = sh (Zmod.sub (Zmod.sub eb c) lz)) by
        (change c with (Zmod.of_Z (2 ^ W) B); unfold shiftV; ring);
      rewrite E end.
    exact eq_refl.
  Qed.

  Definition uexp (u : type (FpUnpK e f)) : bits W := u.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

  (* Range of an unpacked (unbiased) exponent. *)
  Definition URng (u : type (FpUnpK e f)) : Prop :=
    - 2 ^ (e - 1) - f <= Zmod.signed (uexp u) <= 2 ^ (e - 1).

  (* ---------------------------------------------------------------------------
   * (c) RANGES
   * --------------------------------------------------------------------------- *)

  Lemma pW8 : 2 ^ (W - 1) = 8 * 2 ^ (e - 1).
  Proof.
    replace (W - 1) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia.
  Qed.

  Lemma IR_sub_k : forall z Wd k, 0 <= k <= Wd -> - 8 * 2 ^ (e - 1) <= z - Wd -> z + 2 ^ (e - 1) <= 8 * 2 ^ (e - 1) ->
    IR (Zmod.sub (Zmod.of_Z _ z) (Zmod.of_Z _ k)).
  Proof.
    intros z Wd k Hk H1 H2; shtac; rewrite <- Zmod.of_Z_sub; apply InRange_of_Z; try lia;
      rewrite pW8; unfold fpBias; lia.
  Qed.

  Lemma add3_ofZ : forall (a b : bits W) c,
    Zmod.add (Zmod.add (Zmod.add Zmod.zero a) b) (Zmod.of_Z _ c) = Zmod.of_Z _ (Zmod.signed a + Zmod.signed b + c).
  Proof.
    intros a b c; rewrite <- (Zmod.of_Z_signed a) at 1; rewrite <- (Zmod.of_Z_signed b) at 1.
    rewrite <- (Zmod.of_Z_0 (2 ^ W)), <- !Zmod.of_Z_add; f_equal; lia.
  Qed.

  (* Instantiate `normRound_eq` from the goal: `xtac` proves the exponent relation, `rtac` the range. *)
  Ltac nr_step xtac :=
    match goal with |- context [normRound true e f type ?Wd ?s ?x ?w ?st ?r] =>
    match goal with |- context [normRound false e f type Wd ?s' ?x' ?w' ?st' ?r'] =>
      let E := fresh "E" in
      assert (E : x = sh x') by xtac;
      rewrite E, (normRound_eq Wd s x' w st r) end end.

  (* ---------------------------------------------------------------------------
   * (c) OPERATIONS
   * --------------------------------------------------------------------------- *)

  Hypothesis Hfe : 4 * f + 5 <= 6 * 2 ^ (e - 1).

  (* ---- UNPACK RANGE ---- *)
  Lemma ebase_range : forall (bz : bool) (ef : bits e),
    0 <= Zmod.unsigned (evalExpr (ITE (Var type Bool bz) (cst W 1) (Var type (Bit W) (evalExpr (ZeroExtend 3 (Var type (Bit e) ef)))))) < 2 ^ e.
  Proof.
    intros [|] ef.
    - change (0 <= Zmod.unsigned (Zmod.of_Z (2 ^ W) 1) < 2 ^ e).
      rewrite Zmod.unsigned_of_Z, Z.mod_small; [split; [lia | apply Z.pow_gt_1; lia] |].
      split; [lia | apply Z.pow_gt_1; lia].
    - change (0 <= Zmod.unsigned (evalExpr (ZeroExtend 3 (Var type (Bit e) ef))) < 2 ^ e).
      rewrite unsigned_ZeroExtend by lia; apply bits.unsigned_range; lia.
  Qed.

  Lemma unpack_URng : forall a, URng (evalLetExpr (fpUnpack false e f type a)).
  Proof.
    intros a; unfold URng, fpUnpack, expUnpack; cbn [evalLetExpr].
    match goal with |- context [uexp ?X] =>
      match X with context [Sub (Sub (Var _ _ ?eb) ?c) (Var _ _ ?lz)] =>
        assert (Hx : uexp X = Zmod.sub (Zmod.sub eb (Zmod.of_Z (2 ^ W) B)) lz)
          by (unfold uexp; cbn [evalExpr]; rewrite !(sub_eval W ltac:(lia)); exact eq_refl);
        rewrite Hx; clear Hx end end.
    match goal with |- context [Zmod.sub (Zmod.sub ?eb _) ?lz] =>
      match lz with evalExpr (clz ?w ?m ?raw) => destruct (clz_val w m raw ltac:(lia)) as [k [Hk Hc]]; rewrite Hc end;
      match eb with evalExpr (ITE (Var _ _ ?bz) _ (Var _ _ (evalExpr (ZeroExtend _ (Var _ _ ?ef))))) => pose proof (ebase_range bz ef) as He2 end;
      set (ebv := eb) in * end.
    rewrite <- (Zmod.of_Z_unsigned ebv), <- !Zmod.of_Z_sub.
    shtac; assert (2 ^ e = 2 * 2 ^ (e - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite (signed_of_Z_small W ltac:(lia)); try rewrite pW8; unfold fpBias; lia.
  Qed.


  Lemma mulFinish_eq : forall rm ua ub prod, URng ua -> URng ub ->
    evalLetExpr (mulFinish true e f type rm (ukS ua) (ukS ub) prod) = evalLetExpr (mulFinish false e f type rm ua ub prod).
  Proof.
    intros rm ua ub prod Ha Hb; unfold URng in *; unfold mulFinish; cbn [evalLetExpr].
    nr_step ltac:(
      change (Zmod.add (Zmod.add (Zmod.add Zmod.zero (sh (uexp ua))) (sh (uexp ub))) (Zmod.of_Z (2 ^ W) (1 - expOff true e)) =
              sh (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp ua)) (uexp ub)) (Zmod.of_Z (2 ^ W) (1 - expOff false e))));
      unfold expOff, shiftV; rewrite Z.sub_0_r, Zmod.of_Z_sub; ring).
    - exact eq_refl.
    - lia.
    - intros k Hk.
      change (IR (Zmod.sub (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp ua)) (uexp ub)) (Zmod.of_Z (2 ^ W) (1 - expOff false e))) (Zmod.of_Z _ k))).
      rewrite add3_ofZ; apply IR_sub_k with (Wd := 2 * f + 2); unfold expOff; lia.
  Qed.

  (* Rewrites that move the shift out of exponent expressions. *)
  Lemma rd_exp_ukS : forall u, evalExpr (ReadStruct (Var type (FpUnpK e f) (ukS u)) (@Build_FinType 7 5 I)) = sh (uexp u).
  Proof. intros; exact eq_refl. Qed.

  (* `rd_exp_ukS` by `change` on the goal's own terms (much faster than `rewrite` with evars). *)
  Ltac rd_exp :=
    repeat match goal with |- context [@evalExpr ?K (@ReadStruct ?ty ?ls (Var ?ty' ?k (ukS ?u)) (@Build_FinType ?n 5 ?pf))] =>
      change (@evalExpr K (@ReadStruct ty ls (Var ty' k (ukS u)) (@Build_FinType n 5 pf))) with (sh (uexp u)) end.

  Lemma slt_vsh : forall a b, IR a -> IR b ->
    evalExpr (Slt (Var type (Bit W) (sh a)) (Var type (Bit W) (sh b))) = evalExpr (Slt (Var type (Bit W) a) (Var type (Bit W) b)).
  Proof. intros a b Ha Hb; shtac; rewrite !slt_eval by lia; exact (slt_shift W ltac:(lia) B ltac:(lia) a b Ha Hb). Qed.

  Lemma eq_vsh : forall a b,
    evalExpr (Eq (Var type (Bit W) (sh a)) (Var type (Bit W) (sh b))) = evalExpr (Eq (Var type (Bit W) a) (Var type (Bit W) b)).
  Proof. intros a b; exact (shift_eqb W B a b). Qed.

  Lemma ite_vsh : forall (c : bool) a b,
    evalExpr (ITE (Var type Bool c) (Var type (Bit W) (sh a)) (Var type (Bit W) (sh b))) =
    sh (evalExpr (ITE (Var type Bool c) (Var type (Bit W) a) (Var type (Bit W) b))).
  Proof. intros [|] a b; exact eq_refl. Qed.

  Lemma add_vsh : forall a k,
    evalExpr (Add [Var type (Bit W) (sh a); cst W k]) = sh (evalExpr (Add [Var type (Bit W) a; cst W k])).
  Proof.
    intros a k; change (Zmod.add (Zmod.add Zmod.zero (sh a)) (Zmod.of_Z (2 ^ W) k) =
                        sh (Zmod.add (Zmod.add Zmod.zero a) (Zmod.of_Z (2 ^ W) k))); unfold shiftV; ring.
  Qed.

  Lemma alignAdd_eq : forall Wd sB sS xB xS big sm,
    evalLetExpr (alignAdd e type Wd sB sS (sh xB) (sh xS) big sm) = evalLetExpr (alignAdd e type Wd sB sS xB xS big sm).
  Proof.
    intros; unfold alignAdd; cbn [evalLetExpr]; rewrite !(sub_eval W ltac:(lia)).
    match goal with |- context [Zmod.sub (evalExpr (Var _ _ (sh ?a))) (evalExpr (Var _ _ (sh ?b)))] =>
      assert (E : Zmod.sub (evalExpr (Var type (Bit W) (sh a))) (evalExpr (Var type (Bit W) (sh b))) = Zmod.sub a b)
        by exact (shift_sub W B a b); rewrite E end.
    exact eq_refl.
  Qed.

  Lemma URng_IR : forall u, URng u -> IR (uexp u).
  Proof.
    intros u Hu; unfold URng, InRange in *; shtac; rewrite pW8 in *; unfold fpBias; lia.
  Qed.

  (* Range of `max/min(xa, xb) + 1` minus a normalization shift. *)
  Lemma IR_ite_add1 : forall (c : bool) a b Wd k, URng a -> URng b -> 0 <= k <= Wd -> Wd <= f + 5 ->
    IR (Zmod.sub (evalExpr (Add [Var type (Bit W) (evalExpr (ITE (Var type Bool c) (Var type (Bit W) (uexp a)) (Var type (Bit W) (uexp b)))); cst W 1]))
                 (Zmod.of_Z _ k)).
  Proof.
    intros c a b Wd k Ha Hb Hk H2; unfold URng in *.
    assert (Hx : forall x : bits W, - 2 ^ (e - 1) - f <= Zmod.signed x <= 2 ^ (e - 1) ->
              IR (Zmod.sub (Zmod.add (Zmod.add Zmod.zero x) (Zmod.of_Z _ 1)) (Zmod.of_Z _ k))).
    { intros x Hx; rewrite <- (Zmod.of_Z_signed x) at 1; rewrite <- (Zmod.of_Z_0 (2 ^ W)), <- !Zmod.of_Z_add.
      apply IR_sub_k with (Wd := Wd); lia. }
    destruct c; [exact (Hx _ Ha) | exact (Hx _ Hb)].
  Qed.

  Lemma addCore_eq : forall rm a b ua ub, URng ua -> URng ub ->
    evalLetExpr (addCore true e f type rm a b (ukS ua) (ukS ub)) = evalLetExpr (addCore false e f type rm a b ua ub).
  Proof.
    intros rm a b ua ub Ha Hb; unfold addCore; cbn [evalLetExpr].
    rd_exp.
    rewrite (slt_vsh _ _ (URng_IR _ Hb) (URng_IR _ Ha)).
    rewrite eq_vsh.
    rewrite !ite_vsh.
    rewrite alignAdd_eq.
    nr_step ltac:(rewrite add_vsh; exact eq_refl).
    - exact eq_refl.
    - lia.
    - intros k Hk; apply IR_ite_add1 with (Wd := f + 5); auto; lia.
  Qed.

  Lemma IR_k : forall k, - 8 * 2 ^ (e - 1) <= k -> k + 2 ^ (e - 1) <= 8 * 2 ^ (e - 1) -> IR (Zmod.of_Z _ k).
  Proof. intros k H1 H2; shtac; apply InRange_of_Z; try lia; rewrite pW8; unfold fpBias; lia. Qed.

  Lemma IR_add1_k : forall (x : bits W) Wd k, 0 <= k <= Wd ->
    - 8 * 2 ^ (e - 1) <= Zmod.signed x + 1 - Wd -> Zmod.signed x + 1 + 2 ^ (e - 1) <= 8 * 2 ^ (e - 1) ->
    IR (Zmod.sub (Zmod.add (Zmod.add Zmod.zero x) (Zmod.of_Z _ 1)) (Zmod.of_Z _ k)).
  Proof.
    intros x Wd k Hk H1 H2; rewrite <- (Zmod.of_Z_signed x) at 1; rewrite <- (Zmod.of_Z_0 (2 ^ W)), <- !Zmod.of_Z_add.
    apply IR_sub_k with (Wd := Wd); lia.
  Qed.


  Lemma cst_sh : forall k, evalExpr (cst W (k + expOff true e)) = sh (evalExpr (cst W (k + expOff false e))).
  Proof.
    intros k; change (Zmod.of_Z (2 ^ W) (k + expOff true e) = sh (Zmod.of_Z (2 ^ W) (k + expOff false e))).
    unfold expOff; rewrite Z.add_0_r; symmetry; apply shift_of_Z.
  Qed.

  Lemma slt_cv_sh : forall k a, IR (Zmod.of_Z _ k) -> IR a ->
    evalExpr (Slt (cst W (k + expOff true e)) (Var type (Bit W) (sh a))) =
    evalExpr (Slt (cst W (k + expOff false e)) (Var type (Bit W) a)).
  Proof.
    intros k a Hk Ha; shtac; rewrite !slt_eval by lia; rewrite cst_sh.
    change (Z.ltb (Zmod.signed (sh (Zmod.of_Z (2 ^ W) (k + expOff false e)))) (Zmod.signed (sh a)) =
            Z.ltb (Zmod.signed (Zmod.of_Z (2 ^ W) (k + expOff false e))) (Zmod.signed a)).
    unfold expOff; rewrite Z.add_0_r; apply slt_shift; auto; lia.
  Qed.

  Lemma sub_vc_sh : forall k a,
    evalExpr (Sub (Var type (Bit W) (sh a)) (cst W (k + expOff true e))) =
    evalExpr (Sub (Var type (Bit W) a) (cst W (k + expOff false e))).
  Proof.
    intros k a; rewrite !(sub_eval W ltac:(lia)), cst_sh; exact (shift_sub W B a _).
  Qed.

  Lemma sub_cv_sh : forall k a,
    evalExpr (Sub (cst W (k + expOff true e)) (Var type (Bit W) (sh a))) =
    evalExpr (Sub (cst W (k + expOff false e)) (Var type (Bit W) a)).
  Proof.
    intros k a; rewrite !(sub_eval W ltac:(lia)), cst_sh; exact (shift_sub W B _ a).
  Qed.

  Hypothesis Hx0 : 0 <= xlen.
  Hypothesis Hx1 : xlen + 4 <= 7 * 2 ^ (e - 1).

  Lemma fpToInt_eq : forall rm sg w ua, URng ua ->
    evalLetExpr (fpToInt true e f xlen type rm sg w (ukS ua)) = evalLetExpr (fpToInt false e f xlen type rm sg w ua).
  Proof.
    intros rm sg w ua Ha; unfold fpToInt; cbn [evalLetExpr].
    rd_exp.
    rewrite slt_cv_sh by (apply URng_IR, Ha || (apply IR_k; lia)).
    rewrite sub_vc_sh.
    exact eq_refl.
  Qed.

  Lemma intToFp_eq : forall rm sg w x,
    evalLetExpr (intToFp true e f xlen type rm sg w x) = evalLetExpr (intToFp false e f xlen type rm sg w x).
  Proof.
    intros rm sg w x; unfold intToFp; cbn [evalLetExpr].
    nr_step ltac:(apply cst_sh).
    - exact eq_refl.
    - lia.
    - intros k Hk; change (IR (Zmod.sub (Zmod.of_Z (2 ^ W) (xlen - 1 + expOff false e)) (Zmod.of_Z _ k))).
      unfold expOff; apply IR_sub_k with (Wd := xlen + f + 3); lia.
  Qed.

  Lemma fpRound_eq : forall rm nx a ua, URng ua ->
    evalLetExpr (fpRound true e f type rm nx a (ukS ua)) = evalLetExpr (fpRound false e f type rm nx a ua).
  Proof.
    intros rm nx a ua Ha; unfold fpRound; cbn [evalLetExpr].
    rewrite !rd_exp_ukS, slt_cv_sh, sub_cv_sh by (apply URng_IR, Ha || (apply IR_k; lia)).
    nr_step ltac:(apply cst_sh).
    - exact eq_refl.
    - lia.
    - intros k Hk; change (IR (Zmod.sub (Zmod.of_Z (2 ^ W) (f + 3 + expOff false e)) (Zmod.of_Z _ k))).
      unfold expOff; apply IR_sub_k with (Wd := f + 4); lia.
  Qed.

  Lemma xp_sh : forall ua ub (t : bool),
    evalExpr (Add [ReadStruct (Var type (FpUnpK e f) (ukS ua)) (@Build_FinType 7 5 I);
                   ReadStruct (Var type (FpUnpK e f) (ukS ub)) (@Build_FinType 7 5 I);
                   ITE (Var type Bool t) (cst W (1 - expOff true e)) (cst W (0 - expOff true e))]) =
    sh (evalExpr (Add [ReadStruct (Var type (FpUnpK e f) ua) (@Build_FinType 7 5 I);
                       ReadStruct (Var type (FpUnpK e f) ub) (@Build_FinType 7 5 I);
                       ITE (Var type Bool t) (cst W (1 - expOff false e)) (cst W (0 - expOff false e))])).
  Proof.
    intros ua ub [|].
    - change (Zmod.add (Zmod.add (Zmod.add Zmod.zero (sh (uexp ua))) (sh (uexp ub))) (Zmod.of_Z (2 ^ W) (1 - expOff true e)) =
              sh (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp ua)) (uexp ub)) (Zmod.of_Z (2 ^ W) (1 - expOff false e)))).
      unfold expOff, shiftV; rewrite Z.sub_0_r, Zmod.of_Z_sub; ring.
    - change (Zmod.add (Zmod.add (Zmod.add Zmod.zero (sh (uexp ua))) (sh (uexp ub))) (Zmod.of_Z (2 ^ W) (0 - expOff true e)) =
              sh (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp ua)) (uexp ub)) (Zmod.of_Z (2 ^ W) (0 - expOff false e)))).
      unfold expOff, shiftV; rewrite Z.sub_0_r, Zmod.of_Z_sub; ring.
  Qed.

  Lemma xp_val : forall ua ub (t : bool),
    evalExpr (Add [ReadStruct (Var type (FpUnpK e f) ua) (@Build_FinType 7 5 I);
                   ReadStruct (Var type (FpUnpK e f) ub) (@Build_FinType 7 5 I);
                   ITE (Var type Bool t) (cst W (1 - expOff false e)) (cst W (0 - expOff false e))]) =
    Zmod.of_Z _ (Zmod.signed (uexp ua) + Zmod.signed (uexp ub) + (if t then 1 else 0)).
  Proof.
    intros ua ub [|];
      [change (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp ua)) (uexp ub)) (Zmod.of_Z (2 ^ W) (1 - expOff false e)) =
               Zmod.of_Z _ (Zmod.signed (uexp ua) + Zmod.signed (uexp ub) + 1))
      |change (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp ua)) (uexp ub)) (Zmod.of_Z (2 ^ W) (0 - expOff false e)) =
               Zmod.of_Z _ (Zmod.signed (uexp ua) + Zmod.signed (uexp ub) + 0))];
      rewrite add3_ofZ; unfold expOff; f_equal; lia.
  Qed.

  Lemma IR_xp : forall ua ub (t : bool), URng ua -> URng ub ->
    IR (evalExpr (Add [ReadStruct (Var type (FpUnpK e f) ua) (@Build_FinType 7 5 I);
                       ReadStruct (Var type (FpUnpK e f) ub) (@Build_FinType 7 5 I);
                       ITE (Var type Bool t) (cst W (1 - expOff false e)) (cst W (0 - expOff false e))])).
  Proof.
    intros ua ub t Ha Hb; unfold URng in *; rewrite xp_val; apply IR_k; destruct t; lia.
  Qed.

  Lemma IR_fma_xR : forall (c t : bool) ua ub uc k, URng ua -> URng ub -> URng uc -> 0 <= k <= 2 * f + 6 ->
    IR (Zmod.sub (evalExpr (Add [Var type (Bit W) (evalExpr (ITE (Var type Bool c)
            (Var type (Bit W) (evalExpr (Add [ReadStruct (Var type (FpUnpK e f) ua) (@Build_FinType 7 5 I);
                       ReadStruct (Var type (FpUnpK e f) ub) (@Build_FinType 7 5 I);
                       ITE (Var type Bool t) (cst W (1 - expOff false e)) (cst W (0 - expOff false e))])))
            (Var type (Bit W) (uexp uc)))); cst W 1])) (Zmod.of_Z _ k)).
  Proof.
    intros c t ua ub uc k Ha Hb Hc Hk; unfold URng in *; destruct c.
    - change (IR (Zmod.sub (Zmod.add (Zmod.add Zmod.zero (evalExpr (Add [ReadStruct (Var type (FpUnpK e f) ua) (@Build_FinType 7 5 I);
                       ReadStruct (Var type (FpUnpK e f) ub) (@Build_FinType 7 5 I);
                       ITE (Var type Bool t) (cst W (1 - expOff false e)) (cst W (0 - expOff false e))]))) (Zmod.of_Z _ 1)) (Zmod.of_Z _ k))).
      rewrite xp_val; apply IR_add1_k with (Wd := 2 * f + 6); [lia | |];
        (rewrite (signed_of_Z_small W ltac:(lia)); [| rewrite pW8; destruct t; lia]); destruct t; lia.
    - change (IR (Zmod.sub (Zmod.add (Zmod.add Zmod.zero (uexp uc)) (Zmod.of_Z _ 1)) (Zmod.of_Z _ k))).
      apply IR_add1_k with (Wd := 2 * f + 6); lia.
  Qed.

  Lemma fmaFinish_eq : forall rm c ua ub uc negP prod, URng ua -> URng ub -> URng uc ->
    evalLetExpr (fmaFinish true e f type rm c (ukS ua) (ukS ub) (ukS uc) negP prod) =
    evalLetExpr (fmaFinish false e f type rm c ua ub uc negP prod).
  Proof.
    intros rm c ua ub uc negP prod Ha Hb Hc; unfold fmaFinish; cbn [evalLetExpr].
    rd_exp.
    rewrite !xp_sh.
    rewrite slt_vsh by (apply URng_IR, Hc || apply IR_xp; assumption).
    rewrite eq_vsh.
    rewrite !ite_vsh.
    rewrite alignAdd_eq.
    nr_step ltac:(rewrite add_vsh; exact eq_refl).
    - exact eq_refl.
    - lia.
    - intros k Hk; apply IR_fma_xR; assumption.
  Qed.

  (* ---- DIV ---- *)
  Definition dua (i : type (DivInfoK e f)) : type (FpUnpK e f) := i.(Snd).(Fst).
  Definition dub (i : type (DivInfoK e f)) : type (FpUnpK e f) := i.(Snd).(Snd).(Fst).
  Definition diS (i : type (DivInfoK e f)) : type (DivInfoK e f) :=
    (i.(Fst) ,, (ukS i.(Snd).(Fst) ,, (ukS i.(Snd).(Snd).(Fst) ,, tt))).

  Lemma add_sub_ofZ : forall a b : bits W,
    Zmod.add (Zmod.add Zmod.zero (Zmod.sub a b)) (Zmod.of_Z (2 ^ W) 0) = Zmod.of_Z _ (Zmod.signed a - Zmod.signed b).
  Proof.
    intros a b; rewrite <- (Zmod.of_Z_signed a) at 1; rewrite <- (Zmod.of_Z_signed b) at 1.
    rewrite <- (Zmod.of_Z_0 (2 ^ W)), <- Zmod.of_Z_sub, <- !Zmod.of_Z_add; f_equal; lia.
  Qed.

  Lemma divFinishCore_eq : forall i q st, URng (dua i) -> URng (dub i) ->
    evalLetExpr (divFinishCore true e f type (diS i) q st) = evalLetExpr (divFinishCore false e f type i q st).
  Proof.
    intros i q st Ha Hb; unfold URng in *; unfold divFinishCore; cbn [evalLetExpr].
    nr_step ltac:(
      change (Zmod.add (Zmod.add Zmod.zero (Zmod.add (Zmod.add (Zmod.add Zmod.zero (sh (uexp (dua i)))) (Zmod.not (sh (uexp (dub i))))) Zmod.one))
                (Zmod.of_Z (2 ^ W) (expOff true e)) =
              sh (Zmod.add (Zmod.add Zmod.zero (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp (dua i))) (Zmod.not (uexp (dub i)))) Zmod.one))
                (Zmod.of_Z (2 ^ W) (expOff false e))));
      rewrite !(sub_via_not W ltac:(lia)); unfold expOff, shiftV; rewrite Zmod.of_Z_0; ring).
    - exact eq_refl.
    - lia.
    - intros k Hk.
      change (IR (Zmod.sub (Zmod.add (Zmod.add Zmod.zero (Zmod.add (Zmod.add (Zmod.add Zmod.zero (uexp (dua i))) (Zmod.not (uexp (dub i)))) Zmod.one))
                (Zmod.of_Z (2 ^ W) (expOff false e))) (Zmod.of_Z _ k))).
      rewrite (sub_via_not W ltac:(lia)); unfold expOff; rewrite add_sub_ofZ.
      apply IR_sub_k with (Wd := f + 3); lia.
  Qed.

  (* ---- SQRT ---- *)
  Lemma odd_mod_pow : forall a, Z.odd (a mod 2 ^ W) = Z.odd a.
  Proof.
    intros a; shtac; rewrite Z.mod_eq by lia.
    replace (a - 2 ^ W * (a / 2 ^ W)) with (a + 2 * (- (2 ^ (W - 1) * (a / 2 ^ W))))
      by (rewrite (pow_w W ltac:(lia)); ring).
    apply Z.odd_add_mul_2.
  Qed.

  Lemma bitSet0_odd : forall v : bits W, evalExpr (bitSet (ty := type) v 0) = Z.odd (Zmod.to_Z v).
  Proof.
    intros v; shtac.
    change (negb (Zmod.eqb (Zmod.and (Zmod.and (Zmod.of_Z (2 ^ W) (-1)) v) (Zmod.of_Z (2 ^ W) (2 ^ 0)))
                  Zmod.zero) = Z.odd (Zmod.to_Z v)).
    set (Y := Zmod.and (Zmod.and (Zmod.of_Z (2 ^ W) (-1)) v) (Zmod.of_Z (2 ^ W) (2 ^ 0))).
    pose proof (Zmod.unsigned_range v) as Hv.
    assert (HX : Zmod.to_Z Y = Zmod.to_Z v mod 2).
    { unfold Y; rewrite !bits.unsigned_and, !Zmod.unsigned_of_Z.
      assert (Hm : -1 mod 2 ^ W = Z.ones W)
        by (rewrite Z.ones_equiv; symmetry; apply Z.mod_unique with (-1); lia).
      rewrite Hm, (Z.land_comm (Z.ones W)), Z.land_ones, (Z.mod_small (Zmod.to_Z v)) by lia.
      assert (0 < 2 ^ (W - 1)) by (apply Z.pow_pos_nonneg; lia).
      rewrite (Z.mod_small (2 ^ 0)) by (rewrite (pow_w W ltac:(lia)); change (2 ^ 0) with 1; lia).
      change (2 ^ 0) with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity. }
    assert (HY : 0 <= Zmod.to_Z Y < 2) by (rewrite HX; apply Z.mod_pos_bound; lia).
    rewrite Zodd_mod, <- HX.
    destruct (Zmod.eqb_spec Y Zmod.zero) as [E | E].
    - rewrite E, Zmod.unsigned_0; reflexivity.
    - assert (Zmod.to_Z Y <> 0) by (intro Hz; apply E; apply Zmod.unsigned_inj; rewrite Hz, Zmod.unsigned_0; reflexivity).
      replace (Zmod.to_Z Y) with 1 by lia; reflexivity.
  Qed.

  Lemma odd_sh : forall u,
    evalExpr (bitSet (ty := type) (evalExpr (Add [ReadStruct (Var type (FpUnpK e f) (ukS u)) (@Build_FinType 7 5 I);
                                                cst W (expOff true e)])) 0) =
    evalExpr (bitSet (ty := type) (evalExpr (Add [ReadStruct (Var type (FpUnpK e f) u) (@Build_FinType 7 5 I);
                                                cst W (expOff false e)])) 0).
  Proof.
    intros u; rewrite !bitSet0_odd; shtac.
    change (Z.odd (Zmod.to_Z (Zmod.add (Zmod.add Zmod.zero (sh (uexp u))) (Zmod.of_Z (2 ^ W) (expOff true e)))) =
            Z.odd (Zmod.to_Z (Zmod.add (Zmod.add Zmod.zero (uexp u)) (Zmod.of_Z (2 ^ W) (expOff false e))))).
    set (Y := Zmod.add (Zmod.add Zmod.zero (uexp u)) (Zmod.of_Z (2 ^ W) (expOff false e))).
    assert (E : Zmod.add (Zmod.add Zmod.zero (sh (uexp u))) (Zmod.of_Z (2 ^ W) (expOff true e)) = Zmod.add Y (Zmod.of_Z _ (2 * B))).
    { unfold Y, expOff, shiftV; replace (2 * B) with (B + B) by lia; rewrite Zmod.of_Z_add, Zmod.of_Z_0; ring. }
    rewrite E, Zmod.unsigned_add, Zmod.unsigned_of_Z, odd_mod_pow, (Z.mod_small (2 * B))
      by (rewrite (pow_w W ltac:(lia)); lia).
    apply Z.odd_add_mul_2.
  Qed.

  Definition sua (s : type (SqrtStateK e f)) : type (FpUnpK e f) := s.(Fst).(Snd).(Snd).(Fst).
  Definition stS (s : type (SqrtStateK e f)) : type (SqrtStateK e f) :=
    ((s.(Fst).(Fst) ,, (s.(Fst).(Snd).(Fst) ,, (ukS s.(Fst).(Snd).(Snd).(Fst) ,, tt))) ,, s.(Snd)).

  Lemma sqrtStep_stS : forall s, evalLetExpr (sqrtStep e f type (stS s)) = stS (evalLetExpr (sqrtStep e f type s)).
  Proof. intros s; unfold sqrtStep; cbn [evalLetExpr]; exact eq_refl. Qed.

  Lemma sqrtIter_stS : forall n s, evalLetExpr (sqrtIter e f type n (stS s)) = stS (evalLetExpr (sqrtIter e f type n s)).
  Proof.
    induction n as [| n IH]; intros s; [exact eq_refl |].
    cbn [sqrtIter evalLetExpr]; rewrite sqrtStep_stS; apply IH.
  Qed.

  Lemma sqrtIter_info : forall n s, sua (evalLetExpr (sqrtIter e f type n s)) = sua s.
  Proof.
    induction n as [| n IH]; intros s; [reflexivity |].
    cbn [sqrtIter evalLetExpr]; rewrite IH; exact eq_refl.
  Qed.

  Lemma sqrtInit_eq : forall req,
    evalLetExpr (sqrtInit true e f xlen type req) = stS (evalLetExpr (sqrtInit false e f xlen type req)).
  Proof.
    intros req; unfold sqrtInit; cbn [evalLetExpr]; rewrite fpUnpack_shift, odd_sh; exact eq_refl.
  Qed.

  Lemma sra_val : forall u : bits W, - 2 ^ (e - 1) - f <= Zmod.signed u <= 2 ^ (e - 1) ->
    Zmod.signed (Zmod.srs (Zmod.add (Zmod.add Zmod.zero u) (Zmod.of_Z (2 ^ W) 0)) 1) = Zmod.signed u / 2.
  Proof.
    intros u Hu; shtac; rewrite Zmod.signed_srs, Z.shiftr_div_pow2 by lia.
    assert (E : Zmod.add (Zmod.add Zmod.zero u) (Zmod.of_Z (2 ^ W) 0) = u) by (rewrite Zmod.of_Z_0; ring).
    rewrite E; reflexivity.
  Qed.

  Lemma sra_sh : forall u : bits W, - 2 ^ (e - 1) - f <= Zmod.signed u <= 2 ^ (e - 1) ->
    Zmod.srs (Zmod.add (Zmod.add Zmod.zero (sh u)) (Zmod.of_Z (2 ^ W) B)) 1 =
    sh (Zmod.srs (Zmod.add (Zmod.add Zmod.zero u) (Zmod.of_Z (2 ^ W) 0)) 1).
  Proof.
    intros u Hu; shtac; apply Zmod.signed_inj.
    rewrite (signed_shift W ltac:(lia) B ltac:(lia)) by (unfold InRange; rewrite sra_val by lia; rewrite pW8; unfold fpBias in *;
      pose proof (Z.mod_pos_bound (Zmod.signed u) 2); pose proof (Z.div_mod (Zmod.signed u) 2); lia).
    rewrite sra_val by lia.
    rewrite Zmod.signed_srs, Z.shiftr_div_pow2 by lia.
    assert (E : Zmod.add (Zmod.add Zmod.zero (sh u)) (Zmod.of_Z (2 ^ W) B) = Zmod.of_Z _ (Zmod.signed u + B * 2)).
    { unfold shiftV; rewrite <- (Zmod.of_Z_signed u) at 1; rewrite <- (Zmod.of_Z_0 (2 ^ W)), <- !Zmod.of_Z_add; f_equal; lia. }
    rewrite E, (signed_of_Z_small W ltac:(lia)) by (rewrite pW8; unfold fpBias in *; lia).
    change (2 ^ 1) with 2; rewrite Z.div_add by lia; reflexivity.
  Qed.

  Lemma sqrtFinish_eq : forall st, URng (sua st) ->
    evalLetExpr (sqrtFinish true e f type (stS st)) = evalLetExpr (sqrtFinish false e f type st).
  Proof.
    intros st Ha; unfold URng in Ha; unfold sqrtFinish; cbn [evalLetExpr].
    nr_step ltac:(
      change (Zmod.srs (Zmod.add (Zmod.add Zmod.zero (sh (uexp (sua st)))) (Zmod.of_Z (2 ^ W) (expOff true e))) 1 =
              sh (Zmod.srs (Zmod.add (Zmod.add Zmod.zero (uexp (sua st))) (Zmod.of_Z (2 ^ W) (expOff false e))) 1));
      unfold expOff; apply sra_sh; exact Ha).
    - exact eq_refl.
    - lia.
    - intros k Hk.
      change (IR (Zmod.sub (Zmod.srs (Zmod.add (Zmod.add Zmod.zero (uexp (sua st))) (Zmod.of_Z (2 ^ W) (expOff false e))) 1) (Zmod.of_Z _ k))).
      change (IR (Zmod.sub (Zmod.srs (Zmod.add (Zmod.add Zmod.zero (uexp (sua st))) (Zmod.of_Z (2 ^ W) 0)) 1) (Zmod.of_Z _ k))).
      rewrite <- (Zmod.of_Z_signed (Zmod.srs (Zmod.add (Zmod.add Zmod.zero (uexp (sua st))) (Zmod.of_Z (2 ^ W) 0)) 1)), sra_val by exact Ha.
      apply IR_sub_k with (Wd := f + 3); [lia | |];
        (assert (- 2 ^ (e - 1) - f <= 2 * (Zmod.signed (uexp (sua st)) / 2) + 1) by (pose proof (Z.mod_pos_bound (Zmod.signed (uexp (sua st))) 2); pose proof (Z.div_mod (Zmod.signed (uexp (sua st))) 2); lia));
        (assert (2 * (Zmod.signed (uexp (sua st)) / 2) <= 2 ^ (e - 1)) by (pose proof (Z.mod_pos_bound (Zmod.signed (uexp (sua st))) 2); pose proof (Z.div_mod (Zmod.signed (uexp (sua st))) 2); lia));
        lia.
  Qed.

  (* ---- OPERATIONS THAT IGNORE THE EXPONENT ---- *)
  Lemma minMax_ukS : forall isMax nanP a b ua ub,
    evalLetExpr (minMax e f type isMax nanP a b (ukS ua) (ukS ub)) = evalLetExpr (minMax e f type isMax nanP a b ua ub).
  Proof. intros; unfold minMax; cbn [evalLetExpr]; exact eq_refl. Qed.

  Lemma fpCompare_ukS : forall kind quiet a b ua ub,
    evalLetExpr (fpCompare e f xlen type kind quiet a b (ukS ua) (ukS ub)) = evalLetExpr (fpCompare e f xlen type kind quiet a b ua ub).
  Proof. intros; unfold fpCompare; cbn [evalLetExpr]; exact eq_refl. Qed.

  Lemma fpClass_ukS : forall a ua,
    evalLetExpr (fpClass e f xlen type a (ukS ua)) = evalLetExpr (fpClass e f xlen type a ua).
  Proof. intros; unfold fpClass; cbn [evalLetExpr]; exact eq_refl. Qed.

  (* ---------------------------------------------------------------------------
   * (d) ASSEMBLY
   * --------------------------------------------------------------------------- *)

  Definition pua (p : type (PipeInfoK e f xlen)) : type (FpUnpK e f) := p.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition pub (p : type (PipeInfoK e f xlen)) : type (FpUnpK e f) := p.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition puc (p : type (PipeInfoK e f xlen)) : type (FpUnpK e f) := p.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition piS (p : type (PipeInfoK e f xlen)) : type (PipeInfoK e f xlen) :=
    (p.(Fst) ,, (p.(Snd).(Fst) ,, (p.(Snd).(Snd).(Fst) ,, (p.(Snd).(Snd).(Snd).(Fst) ,,
    (p.(Snd).(Snd).(Snd).(Snd).(Fst) ,, (p.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,,
    (ukS (pua p) ,, (ukS (pub p) ,, (ukS (puc p) ,,
    (p.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt)))))))))).

  Lemma pipeInfoOf_eq : forall req,
    evalLetExpr (pipeInfoOf true e f xlen type req) = piS (evalLetExpr (pipeInfoOf false e f xlen type req)).
  Proof. intros; unfold pipeInfoOf; cbn [evalLetExpr]; rewrite !fpUnpack_shift; exact eq_refl. Qed.

  Lemma pipeFinishCore_eq : forall info prod, URng (pua info) -> URng (pub info) -> URng (puc info) ->
    evalLetExpr (pipeFinishCore true e f xlen type (piS info) prod) = evalLetExpr (pipeFinishCore false e f xlen type info prod).
  Proof.
    intros info prod Ha Hb Hc; unfold pipeFinishCore; cbn [evalLetExpr].
    match goal with |- context [addCore true e f type ?rm ?a ?b ?ut ?vt] =>
    match goal with |- context [addCore false e f type _ _ _ ?u ?v] =>
      change ut with (ukS u); change vt with (ukS v); rewrite (addCore_eq rm a b u v Ha Hb) end end.
    match goal with |- context [mulFinish true e f type ?rm ?ut ?vt ?pr] =>
    match goal with |- context [mulFinish false e f type _ ?u ?v _] =>
      change ut with (ukS u); change vt with (ukS v); rewrite (mulFinish_eq rm u v pr Ha Hb) end end.
    match goal with |- context [fmaFinish true e f type ?rm ?c ?ut ?vt ?wt ?np ?pr] =>
    match goal with |- context [fmaFinish false e f type _ _ ?u ?v ?w _ _] =>
      change ut with (ukS u); change vt with (ukS v); change wt with (ukS w);
      rewrite (fmaFinish_eq rm c u v w np pr Ha Hb Hc) end end.
    match goal with |- context [minMax e f type ?im ?np ?a ?b ?ut ?vt] =>
    match goal with |- context [minMax e f type _ _ _ _ ?u ?v] =>
      tryif constr_eq ut u then fail else
      (change ut with (ukS u); change vt with (ukS v); rewrite (minMax_ukS im np a b u v)) end end.
    match goal with |- context [fpToInt true e f xlen type ?rm ?sg ?w ?ut] =>
    match goal with |- context [fpToInt false e f xlen type _ _ _ ?u] =>
      change ut with (ukS u); rewrite (fpToInt_eq rm sg w u Ha) end end.
    rewrite intToFp_eq.
    match goal with |- context [fpCompare e f xlen type ?k ?q ?a ?b ?ut ?vt] =>
    match goal with |- context [fpCompare e f xlen type _ _ _ _ ?u ?v] =>
      tryif constr_eq ut u then fail else
      (change ut with (ukS u); change vt with (ukS v); rewrite (fpCompare_ukS k q a b u v)) end end.
    match goal with |- context [fpClass e f xlen type ?a ?ut] =>
    match goal with |- context [fpClass e f xlen type _ ?u] =>
      tryif constr_eq ut u then fail else (change ut with (ukS u); rewrite (fpClass_ukS a u)) end end.
    match goal with |- context [fpRound true e f type ?rm ?nx ?a ?ut] =>
    match goal with |- context [fpRound false e f type _ _ _ ?u] =>
      change ut with (ukS u); rewrite (fpRound_eq rm nx a u Ha) end end.
    exact eq_refl.
  Qed.

  Lemma pipeSpec_eq : forall req,
    evalLetExpr (pipeSpec true e f xlen type req) = evalLetExpr (pipeSpec false e f xlen type req).
  Proof.
    intros req; unfold pipeSpec; cbn [evalLetExpr]; rewrite pipeInfoOf_eq.
    rewrite pipeFinishCore_eq by apply unpack_URng.
    exact eq_refl.
  Qed.

  Lemma divInfoOf_eq : forall req,
    evalLetExpr (divInfoOf true e f xlen type req) = diS (evalLetExpr (divInfoOf false e f xlen type req)).
  Proof. intros; unfold divInfoOf; cbn [evalLetExpr]; rewrite !fpUnpack_shift; exact eq_refl. Qed.

  Lemma divSpec_eq : forall req,
    evalLetExpr (divSpec true e f xlen type req) = evalLetExpr (divSpec false e f xlen type req).
  Proof.
    intros req; unfold divSpec; cbn [evalLetExpr]; rewrite divInfoOf_eq.
    rewrite divFinishCore_eq by apply unpack_URng.
    exact eq_refl.
  Qed.

  Lemma sqrtSpec_eq : forall req,
    evalLetExpr (sqrtSpec true e f xlen type req) = evalLetExpr (sqrtSpec false e f xlen type req).
  Proof.
    intros req; unfold sqrtSpec; cbn [evalLetExpr]; rewrite sqrtInit_eq, sqrtIter_stS, sqrtFinish_eq.
    - exact eq_refl.
    - rewrite sqrtIter_info; apply unpack_URng.
  Qed.

  Theorem fpuCompute_bm_equiv : forall req,
    evalLetExpr (fpuCompute false e f xlen type req) = evalLetExpr (fpuCompute true e f xlen type req).
  Proof.
    intros req; unfold fpuCompute; cbn [evalLetExpr]; rewrite pipeSpec_eq, divSpec_eq, sqrtSpec_eq; exact eq_refl.
  Qed.
End Equiv.

(* ===========================================================================
 * FORMAT CONVERSION
 * =========================================================================== *)

Section CvtEquiv.
  Variable e1 f1 e2 f2 : Z.
  Hypothesis He1 : 2 <= e1.
  Hypothesis Hf1 : 2 <= f1.
  Hypothesis Hfe1 : 4 * f1 + 5 <= 6 * 2 ^ (e1 - 1).
  Hypothesis He2 : 2 <= e2.
  Hypothesis Hf2 : 2 <= f2.
  Hypothesis Hfe2 : 4 * f2 + 5 <= 6 * 2 ^ (e2 - 1).

  Local Abbreviation ew := (Z.max e1 e2 + 3).
  Local Abbreviation ww := (Z.max (f1 + 1) (f2 + 3)).
  Local Abbreviation B1 := (fpBias e1).
  Local Abbreviation B2 := (fpBias e2).
  Local Abbreviation shw := (shiftV ew B2).
  Local Abbreviation IRw := (InRange ew B2).

  Add Ring zringEW : (Zmod.ring_theory (2 ^ ew)).
  Add Ring zringE2 : (Zmod.ring_theory (2 ^ (e2 + 3))).

  Lemma pow_ew : 8 * 2 ^ (e1 - 1) <= 2 ^ (ew - 1) /\ 8 * 2 ^ (e2 - 1) <= 2 ^ (ew - 1).
  Proof.
    replace (ew - 1) with (Z.max e1 e2 + 2) by lia.
    split; replace 8 with (2 ^ 3) by reflexivity; rewrite <- Z.pow_add_r by lia;
      apply Z.pow_le_mono_r; lia.
  Qed.

  Lemma B2_rng : 0 <= B2 < 2 ^ (ew - 1).
  Proof.
    pose proof pow_ew; unfold fpBias; assert (0 < 2 ^ (e2 - 1)) by (apply Z.pow_pos_nonneg; lia); lia.
  Qed.

  Local Ltac ewtac := pose proof pow_ew; pose proof B2_rng; assert (0 < 2 ^ (e1 - 1)) by (apply Z.pow_pos_nonneg; lia);
    assert (0 < 2 ^ (e2 - 1)) by (apply Z.pow_pos_nonneg; lia).

  (* Sign extension through the top-bit flip. *)
  Lemma x1_val : forall (v : bits (e1 + 3)) C,
    evalExpr (Add [zext (e1 + 3) ew (Xor [Var type (Bit (e1 + 3)) v; cst (e1 + 3) (2 ^ (e1 + 2))]); cst ew C]) =
    Zmod.of_Z _ (Zmod.signed v + 2 ^ (e1 + 2) + C).
  Proof.
    intros v C.
    assert (Hz : Zmod.to_Z (evalExpr (zext (e1 + 3) ew (Xor [Var type (Bit (e1 + 3)) v; cst (e1 + 3) (2 ^ (e1 + 2))])))
                 = Zmod.signed v + 2 ^ (e1 + 2)).
    { rewrite unsigned_zext by lia.
      cbn [evalExpr fold_left map evalXorBinary evalBinary KindCustomInd getDefault].
      rewrite bits_xor_0_l. replace (e1 + 2) with (e1 + 3 - 1) by lia. apply xor_top; lia. }
    change (Zmod.add (Zmod.add Zmod.zero (evalExpr (zext (e1 + 3) ew (Xor [Var type (Bit (e1 + 3)) v; cst (e1 + 3) (2 ^ (e1 + 2))]))))
              (Zmod.of_Z (2 ^ ew) C) = Zmod.of_Z _ (Zmod.signed v + 2 ^ (e1 + 2) + C)).
    rewrite <- (Zmod.of_Z_unsigned (evalExpr (zext _ _ _))), Hz, <- (Zmod.of_Z_0 (2 ^ ew)), <- !Zmod.of_Z_add.
    f_equal; lia.
  Qed.

  Lemma x1_rel : forall u : bits (e1 + 3), InRange (e1 + 3) B1 u ->
    Zmod.of_Z (2 ^ ew) (Zmod.signed (shiftV (e1 + 3) B1 u) + 2 ^ (e1 + 2) + (expOff true e2 - expOff true e1 - 2 ^ (e1 + 2))) =
    shw (Zmod.of_Z (2 ^ ew) (Zmod.signed u + 2 ^ (e1 + 2) + (expOff false e2 - expOff false e1 - 2 ^ (e1 + 2)))).
  Proof.
    intros u Hu; ewtac.
    rewrite (signed_shift (e1 + 3) ltac:(lia) B1) by (try exact Hu; unfold fpBias;
      replace (e1 + 3 - 1) with ((e1 - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    rewrite shift_of_Z by lia. unfold expOff; f_equal; lia.
  Qed.

  Lemma cstw_sh : forall k, evalExpr (cst ew (k + expOff true e2)) = shw (evalExpr (cst ew (k + expOff false e2))).
  Proof.
    intros k; change (Zmod.of_Z (2 ^ ew) (k + expOff true e2) = shw (Zmod.of_Z (2 ^ ew) (k + expOff false e2))).
    unfold expOff; rewrite Z.add_0_r; symmetry; apply shift_of_Z.
  Qed.

  Lemma sltw_vsh : forall a b, IRw a -> IRw b ->
    evalExpr (Slt (Var type (Bit ew) (shw a)) (Var type (Bit ew) (shw b))) = evalExpr (Slt (Var type (Bit ew) a) (Var type (Bit ew) b)).
  Proof. intros a b Ha Hb; ewtac; rewrite !slt_eval by lia; exact (slt_shift ew ltac:(lia) B2 B2_rng a b Ha Hb). Qed.

  Lemma ite2_vsh : forall (c1 c2 : bool) a b c,
    evalExpr (ITE (Var type Bool c1) (Var type (Bit ew) (shw a))
               (ITE (Var type Bool c2) (Var type (Bit ew) (shw b)) (Var type (Bit ew) (shw c)))) =
    shw (evalExpr (ITE (Var type Bool c1) (Var type (Bit ew) a)
               (ITE (Var type Bool c2) (Var type (Bit ew) b) (Var type (Bit ew) c)))).
  Proof. intros [|] [|] a b c; exact eq_refl. Qed.

  Lemma trunc_sh : forall y : bits ew,
    evalExpr (trunc ew (e2 + 3) (Var type (Bit ew) (shw y))) =
    shiftV (e2 + 3) B2 (evalExpr (trunc ew (e2 + 3) (Var type (Bit ew) y))).
  Proof.
    intros y; ewtac; apply Zmod.unsigned_inj.
    assert (Hd : (2 ^ (e2 + 3) | 2 ^ ew))
      by (exists (2 ^ (ew - (e2 + 3))); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    unfold shiftV; rewrite Zmod.unsigned_add, !unsigned_trunc by lia; cbn [evalExpr].
    rewrite Zmod.unsigned_add, !Zmod.unsigned_of_Z, Z.mod_mod_divide by exact Hd.
    assert (2 ^ ew = 2 * 2 ^ (ew - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite (Z.mod_small B2 (2 ^ ew)) by lia.
    rewrite <- Zplus_mod; reflexivity.
  Qed.

  Lemma ew_div : (2 ^ (e2 + 3) | 2 ^ ew).
  Proof. exists (2 ^ (ew - (e2 + 3))); rewrite <- Z.pow_add_r by lia; f_equal; lia. Qed.

  Lemma trunc_ofZ : forall y : bits ew,
    evalExpr (trunc ew (e2 + 3) (Var type (Bit ew) y)) = Zmod.of_Z (2 ^ (e2 + 3)) (Zmod.signed y).
  Proof.
    intros y; apply Zmod.unsigned_inj; rewrite unsigned_trunc by lia; cbn [evalExpr].
    rewrite Zmod.unsigned_of_Z, <- (Zmod.of_Z_signed y) at 1.
    rewrite Zmod.unsigned_of_Z, Z.mod_mod_divide by exact ew_div; reflexivity.
  Qed.

  Lemma clamp_rng : forall x1 lo hi : bits ew, Zmod.signed lo <= Zmod.signed hi ->
    Zmod.signed lo <= Zmod.signed (evalExpr (ITE (Var type Bool (evalExpr (Slt (Var type (Bit ew) x1) (Var type (Bit ew) lo))))
        (Var type (Bit ew) lo)
        (ITE (Var type Bool (evalExpr (Slt (Var type (Bit ew) hi) (Var type (Bit ew) x1)))) (Var type (Bit ew) hi) (Var type (Bit ew) x1))))
    <= Zmod.signed hi.
  Proof.
    intros x1 lo hi H; rewrite !slt_eval by lia; cbn [evalExpr].
    destruct (Z.ltb_spec (Zmod.signed x1) (Zmod.signed lo)); [lia |].
    destruct (Z.ltb_spec (Zmod.signed hi) (Zmod.signed x1)); lia.
  Qed.

  Lemma IR2_X2 : forall x1 lo hi : bits ew,
    Zmod.signed lo = fpEmin e2 - (f2 + 4) -> Zmod.signed hi = fpEmax e2 + 1 ->
    InRange (e2 + 3) B2 (evalExpr (trunc ew (e2 + 3) (Var type (Bit ew)
      (evalExpr (ITE (Var type Bool (evalExpr (Slt (Var type (Bit ew) x1) (Var type (Bit ew) lo))))
        (Var type (Bit ew) lo)
        (ITE (Var type Bool (evalExpr (Slt (Var type (Bit ew) hi) (Var type (Bit ew) x1)))) (Var type (Bit ew) hi) (Var type (Bit ew) x1))))))).
  Proof.
    intros x1 lo hi Hl Hh; ewtac.
    pose proof (clamp_rng x1 lo hi ltac:(rewrite Hl, Hh; unfold fpEmin, fpEmax, fpBias; lia)) as Hc.
    rewrite trunc_ofZ; apply InRange_of_Z; try lia;
      replace (e2 + 3 - 1) with ((e2 - 1) + 3) by lia; rewrite Z.pow_add_r by lia;
      rewrite Hl, Hh in Hc; unfold fpEmin, fpEmax, fpBias in *; lia.
  Qed.

  Lemma wsig_ge : forall sig : bits (f1 + 1), 2 ^ f1 <= Zmod.to_Z sig ->
    2 ^ (ww - 1) <= Zmod.to_Z (evalExpr (Sll (zext (f1 + 1) ww (Var type (Bit (f1 + 1)) sig)) (cst ww (ww - (f1 + 1))))).
  Proof.
    intros sig Hs.
    pose proof (bits.unsigned_range sig ltac:(lia)) as Hr.
    change (2 ^ (ww - 1) <= Zmod.to_Z (Zmod.slu (evalExpr (zext (f1 + 1) ww (Var type (Bit (f1 + 1)) sig)))
                                         (Zmod.to_Z (Zmod.of_Z (2 ^ ww) (ww - (f1 + 1)))))).
    assert (Hk : Zmod.to_Z (Zmod.of_Z (2 ^ ww) (ww - (f1 + 1))) = ww - (f1 + 1)).
    { rewrite Zmod.unsigned_of_Z; apply Z.mod_small; split; [lia |].
      apply Z.lt_le_trans with (2 ^ (ww - (f1 + 1))); [apply Z.pow_gt_lin_r; lia | apply Z.pow_le_mono_r; lia]. }
    rewrite Zmod.unsigned_slu, Hk, unsigned_zext by lia; cbn [evalExpr].
    rewrite Z.shiftl_mul_pow2 by lia.
    assert (Hp : 2 ^ ww = 2 ^ (f1 + 1) * 2 ^ (ww - (f1 + 1))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hq : 2 ^ (ww - 1) = 2 ^ f1 * 2 ^ (ww - (f1 + 1))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ (ww - (f1 + 1))) by (apply Z.pow_pos_nonneg; lia).
    rewrite Z.mod_small by (split; [nia | rewrite Hp; nia]).
    rewrite Hq; nia.
  Qed.

  Theorem cvtFF_bm_equiv : forall rm a,
    evalLetExpr (cvtFF false e1 f1 e2 f2 type rm a) = evalLetExpr (cvtFF true e1 f1 e2 f2 type rm a).
  Proof.
    intros rm a; symmetry; unfold cvtFF; cbn [evalLetExpr].
    pose proof (fpUnpack_sig_ge e1 f1 a ltac:(lia)) as Hsig.
    rewrite (fpUnpack_shift e1 f1 He1) in *.
    set (U := evalLetExpr (fpUnpack false e1 f1 type a)) in *.
    assert (HU : URng e1 f1 U) by exact (unpack_URng e1 f1 He1 Hf1 Hfe1 a).
    assert (HI : InRange (e1 + 3) B1 (uexp e1 f1 U)) by exact (URng_IR e1 f1 He1 Hf1 Hfe1 U HU).
    unfold URng in HU.
    rewrite !x1_val.
    repeat match goal with |- context [@evalExpr ?K (@ReadStruct ?ty ?ls (Var ?ty' ?k (ukS e1 f1 U)) (@Build_FinType ?n 5 ?pf))] =>
      change (@evalExpr K (@ReadStruct ty ls (Var ty' k (ukS e1 f1 U)) (@Build_FinType n 5 pf))) with (shiftV (e1 + 3) B1 (uexp e1 f1 U)) end.
    repeat match goal with |- context [@evalExpr ?K (@ReadStruct ?ty ?ls (Var ?ty' ?k U) (@Build_FinType ?n 5 ?pf))] =>
      change (@evalExpr K (@ReadStruct ty ls (Var ty' k U) (@Build_FinType n 5 pf))) with (uexp e1 f1 U) end.
    rewrite (x1_rel _ HI), !cstw_sh.
    rewrite !sltw_vsh by
      (ewtac; first [ match goal with |- InRange _ _ (evalExpr (cst ?w ?c)) => change (InRange ew B2 (Zmod.of_Z (2 ^ w) c)) end
                    | idtac ];
       apply InRange_of_Z; try lia; unfold expOff, fpEmin, fpEmax, fpBias in *; lia).
    rewrite ite2_vsh, trunc_sh.
    match goal with |- context [normRound true e2 f2 type ?Wd ?s (shiftV _ _ ?x) ?w ?st ?r] =>
      rewrite (normRound_eq0 e2 f2 He2 Wd s x w st r) end.
    - exact eq_refl.
    - apply clz_top; [lia |]. apply wsig_ge. exact Hsig.
    - apply IR2_X2;
        match goal with |- Zmod.signed (evalExpr (cst ?w ?c)) = ?r => change (Zmod.signed (Zmod.of_Z (2 ^ w) c) = r) end;
        ewtac; unfold expOff; rewrite Z.add_0_r; apply (signed_of_Z_small ew ltac:(lia));
        unfold fpEmin, fpEmax, fpBias in *; lia.
  Qed.
End CvtEquiv.

(* ===========================================================================
 * THE REFERENCE MODEL (`FpCoreRef.v`)
 * =========================================================================== *)

(* The format condition: `2 <= f` and Flocq's `f + 1 < 2^(e-1)` (precision below emax).  It implies
 * everything the proofs above use. *)
Lemma fmt_cond : forall e f, 2 <= f -> f + 1 < 2 ^ (e - 1) -> 2 <= e /\ 4 * f + 5 <= 6 * 2 ^ (e - 1).
Proof.
  intros e f Hf Hp.
  assert (He : 2 <= e).
  { destruct (Z_lt_le_dec (e - 1) 0) as [Hn | Hn]; [rewrite Z.pow_neg_r in Hp by lia; lia |].
    destruct (Z_lt_le_dec (e - 1) 1) as [H1 | H1]; [replace (e - 1) with 0 in Hp by lia; cbn in Hp; lia | lia]. }
  split; [exact He | lia].
Qed.

Theorem fpuComputeRef_equiv : forall e f xlen, 2 <= f -> f + 1 < 2 ^ (e - 1) ->
  0 <= xlen -> xlen + 4 <= 7 * 2 ^ (e - 1) ->
  forall req, evalLetExpr (fpuComputeRef e f xlen type req) = evalLetExpr (fpuCompute true e f xlen type req).
Proof.
  intros e f xlen Hf Hp Hx0 Hx1; destruct (fmt_cond e f Hf Hp) as [He Hfe].
  exact (fpuCompute_bm_equiv e f xlen He Hf Hfe Hx0 Hx1).
Qed.

Theorem cvtFFRef_equiv : forall e1 f1 e2 f2,
  2 <= f1 -> f1 + 1 < 2 ^ (e1 - 1) -> 2 <= f2 -> f2 + 1 < 2 ^ (e2 - 1) ->
  forall rm a, evalLetExpr (cvtFFRef e1 f1 e2 f2 type rm a) = evalLetExpr (cvtFF true e1 f1 e2 f2 type rm a).
Proof.
  intros e1 f1 e2 f2 Hf1 Hp1 Hf2 Hp2.
  destruct (fmt_cond e1 f1 Hf1 Hp1) as [He1 Hfe1]; destruct (fmt_cond e2 f2 Hf2 Hp2) as [He2 Hfe2].
  exact (cvtFF_bm_equiv e1 f1 e2 f2 He1 Hf1 Hfe1 He2 Hf2 Hfe2).
Qed.
