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
 * Bit-vector facts for exponent offsets (`ExpShift.v`).
 *
 * The biased and the unbiased exponent models of `FpCore.v` differ by a constant offset on the
 * `w`-bit internal exponents.  This file proves the generic facts the equivalence needs:
 * - `slt_eval`: the signed comparison `Slt` of `FpUtil.v` compares `Zmod.signed` values;
 * - `signed_shift`: adding an offset does not wrap when the result stays in the signed range;
 * - the shift is invisible to differences, equalities and (in range) signed comparisons.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil.

Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------
 * 1. SIGNED COMPARISON
 * --------------------------------------------------------------------------- *)

Lemma bits_xor_0_l : forall n (x : bits n), Zmod.xor Zmod.zero x = x.
Proof. intros n x; apply Zmod.unsigned_inj; rewrite bits.unsigned_xor, Zmod.unsigned_0; apply Z.lxor_0_l. Qed.

Lemma land_lt_pow2 : forall y n, 0 <= n -> 0 <= y < 2 ^ n -> Z.land y (2 ^ n) = 0.
Proof.
  intros y n Hn Hy; apply Z.bits_inj'; intros i Hi.
  rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec n i) as [-> | _]; [| apply andb_false_r].
  rewrite andb_true_r, <- (Z.mod_small y (2 ^ i)) by lia; apply Z.mod_pow2_bits_high; lia.
Qed.

(* XOR with the top bit adds `2^(w-1)` to the signed value. *)
Lemma xor_top : forall w (x : bits w), 1 <= w ->
  Zmod.to_Z (Zmod.xor x (Zmod.of_Z (2 ^ w) (2 ^ (w - 1)))) = Zmod.signed x + 2 ^ (w - 1).
Proof.
  intros w x Hw.
  assert (Hk : Zmod.to_Z (Zmod.of_Z (2 ^ w) (2 ^ (w - 1))) = 2 ^ (w - 1)).
  { rewrite Zmod.unsigned_of_Z; apply Z.mod_small; split; [lia | apply Z.pow_lt_mono_r; lia]. }
  assert (Hpw : 2 ^ w = 2 * 2 ^ (w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  pose proof (Zmod.unsigned_range x) as Hr.
  rewrite bits.unsigned_xor, Hk.
  destruct (Z.ltb_spec (Zmod.to_Z x) (2 ^ (w - 1))) as [Hlt | Hge].
  - rewrite Zmod.signed_small by lia.
    rewrite <- Z.add_nocarry_lxor; [reflexivity |].
    apply land_lt_pow2; lia.
  - rewrite Zmod.signed_large by lia.
    set (y := Zmod.to_Z x - 2 ^ (w - 1)).
    assert (Hx : Zmod.to_Z x = Z.lxor y (2 ^ (w - 1))).
    { rewrite <- Z.add_nocarry_lxor by (apply land_lt_pow2; lia). unfold y; lia. }
    rewrite Hx at 1; rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. unfold y; lia.
Qed.

Lemma slt_eval : forall w (a b : Expr type (Bit w)), 1 <= w ->
  evalExpr (Slt a b) = Z.ltb (Zmod.signed (evalExpr a)) (Zmod.signed (evalExpr b)).
Proof.
  intros w a b Hw; unfold Slt, cst; cbn [evalExpr fold_left map evalXorBinary evalBinary KindCustomInd getDefault].
  rewrite !bits_xor_0_l, !xor_top by exact Hw.
  destruct (Z.ltb_spec (Zmod.signed (evalExpr a) + 2 ^ (w - 1)) (Zmod.signed (evalExpr b) + 2 ^ (w - 1)));
  destruct (Z.ltb_spec (Zmod.signed (evalExpr a)) (Zmod.signed (evalExpr b))); lia.
Qed.

(* `Sub a b` is `Add [a; Not b; 1]`; it evaluates to `Zmod.sub`. *)
Lemma add_not : forall w (x : bits w), 0 <= w -> Zmod.add x (Zmod.not x) = Zmod.opp Zmod.one.
Proof.
  intros w x Hw. apply Zmod.unsigned_inj.
  rewrite Zmod.unsigned_add, bits.unsigned_not', Zmod.unsigned_opp, Zmod.unsigned_1, Z.ones_equiv.
  pose proof (Zmod.unsigned_range x).
  assert (0 < 2 ^ w) by lia.
  replace (Zmod.to_Z x + (Z.pred (2 ^ w) - Zmod.to_Z x)) with (- 1 + 1 * 2 ^ w) by lia.
  rewrite Z.mod_add by lia.
  destruct (Z.eq_dec (2 ^ w) 1) as [E | E].
  - rewrite E; reflexivity.
  - rewrite (Z.mod_small 1) by lia; reflexivity.
Qed.

Section SubEval.
  Variable w : Z.
  Hypothesis Hw : 0 <= w.
  Add Ring zringS : (Zmod.ring_theory (2 ^ w)).

  Lemma sub_via_not : forall (x y : Zmod (2 ^ w)),
    Zmod.add (Zmod.add (Zmod.add Zmod.zero x) (Zmod.not y)) Zmod.one = Zmod.sub x y.
  Proof.
    intros x y; pose proof (add_not w y Hw) as H.
    replace (Zmod.not y) with (Zmod.sub (Zmod.add y (Zmod.not y)) y) by ring.
    rewrite H; ring.
  Qed.

  Lemma sub_eval : forall (a b : Expr type (Bit w)),
    evalExpr (Sub a b) = Zmod.sub (evalExpr a) (evalExpr b).
  Proof.
    intros a b; unfold Sub; cbn [evalExpr fold_left map evalBinary evalNot KindCustomInd getDefault].
    exact (sub_via_not _ _).
  Qed.
End SubEval.

(* `clz` is a count in `[0, w]`. *)
Lemma clz_val : forall w m (x : type (Bit w)), 0 <= w ->
  exists k, 0 <= k <= w /\ evalExpr (clz w m x) = Zmod.of_Z _ k.
Proof.
  intros w m x Hw; unfold clz.
  assert (G : forall l (acc : Expr type (Bit m)),
             (exists k, 0 <= k <= w /\ evalExpr acc = Zmod.of_Z _ k) ->
             Forall (fun i => 0 <= i < w) l ->
             exists k, 0 <= k <= w /\
               evalExpr (fold_left (fun acc i => ITE (bitSet x i) (cst m (w - 1 - i)) acc) l acc) = Zmod.of_Z _ k).
  { induction l as [| a l IH]; intros acc Hacc Hl; [exact Hacc |].
    inversion Hl as [| ? ? Ha Hl']; subst; cbn [fold_left]; apply IH; [| exact Hl'].
    cbn [evalExpr]; destruct (evalExpr (bitSet x a)); [exists (w - 1 - a); split; [lia | reflexivity] | exact Hacc]. }
  apply G; [exists w; split; [lia | reflexivity] |].
  apply Forall_forall; intros i Hi; apply in_map_iff in Hi as [n [<- Hn]]; apply in_seq in Hn; lia.
Qed.

(* `bitSet x i` is bit `i` of `x`. *)
Lemma bitSet_testbit : forall w (x : bits w) i, 0 <= i < w ->
  evalExpr (bitSet (ty := type) x i) = Z.testbit (Zmod.to_Z x) i.
Proof.
  intros w x i Hi.
  change (negb (Zmod.eqb (Zmod.and (Zmod.and (Zmod.of_Z (2 ^ w) (-1)) x) (Zmod.of_Z (2 ^ w) (2 ^ i)))
                Zmod.zero) = Z.testbit (Zmod.to_Z x) i).
  set (Y := Zmod.and (Zmod.and (Zmod.of_Z (2 ^ w) (-1)) x) (Zmod.of_Z (2 ^ w) (2 ^ i))).
  pose proof (Zmod.unsigned_range x) as Hv.
  assert (Hpi : 0 < 2 ^ i < 2 ^ w) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_lt_mono_r]; lia).
  assert (HX : Zmod.to_Z Y = Z.land (Zmod.to_Z x) (2 ^ i)).
  { unfold Y; rewrite !bits.unsigned_and, !Zmod.unsigned_of_Z.
    assert (Hm : -1 mod 2 ^ w = Z.ones w)
      by (rewrite Z.ones_equiv; symmetry; apply Z.mod_unique with (-1); lia).
    rewrite Hm, (Z.land_comm (Z.ones w)), Z.land_ones, !Z.mod_small by lia; reflexivity. }
  destruct (Z.testbit (Zmod.to_Z x) i) eqn:Ht.
  - destruct (Zmod.eqb_spec Y Zmod.zero) as [E | E]; [| reflexivity].
    exfalso; apply (f_equal Zmod.to_Z) in E; rewrite HX, Zmod.unsigned_0 in E.
    assert (Z.testbit (Z.land (Zmod.to_Z x) (2 ^ i)) i = true)
      by (rewrite Z.land_spec, Ht, Z.pow2_bits_true by lia; reflexivity).
    rewrite E, Z.bits_0 in H; discriminate.
  - destruct (Zmod.eqb_spec Y Zmod.zero) as [E | E]; [reflexivity |].
    exfalso; apply E, Zmod.unsigned_inj; rewrite HX, Zmod.unsigned_0.
    apply Z.bits_inj'; intros j Hj; rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec i j) as [<- | _]; [rewrite Ht |]; apply andb_false_r || reflexivity.
Qed.

(* A value with its top bit set has no leading zeros. *)
Lemma clz_top : forall w m (x : bits w), 1 <= w -> 2 ^ (w - 1) <= Zmod.to_Z x ->
  evalExpr (clz w m x) = Zmod.of_Z _ 0.
Proof.
  intros w m x Hw Hx; unfold clz.
  replace (Z.to_nat w) with (S (Z.to_nat (w - 1))) by lia.
  rewrite seq_S, map_app, fold_left_app; cbn [fold_left map].
  replace (Z.of_nat (0 + Z.to_nat (w - 1))) with (w - 1) by lia.
  cbn [evalExpr]; rewrite bitSet_testbit by lia.
  pose proof (Zmod.unsigned_range x) as Hv.
  assert (Hb : Z.testbit (Zmod.to_Z x) (w - 1) = true).
  { apply Z.testbit_true; [lia |].
    assert (Hpw : 2 ^ w = 2 * 2 ^ (w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hq : Zmod.to_Z x / 2 ^ (w - 1) = 1)
      by (symmetry; apply Z.div_unique with (Zmod.to_Z x - 2 ^ (w - 1)); lia).
    rewrite Hq; reflexivity. }
  rewrite Hb; replace (w - 1 - (w - 1)) with 0 by lia; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
 * 2. SHIFTED VALUES
 * --------------------------------------------------------------------------- *)

Section Shift.
  Variable w : Z.
  Hypothesis Hw : 1 <= w.
  Variable B : Z.
  Hypothesis HB : 0 <= B < 2 ^ (w - 1).

  Local Abbreviation bw := (bits w).

  Add Ring zring : (Zmod.ring_theory (2 ^ w)).

  Definition shiftV (x : bw) : bw := Zmod.add x (Zmod.of_Z _ B).

  (* In range: the signed value and its shift both fit. *)
  Definition InRange (x : bw) : Prop := - 2 ^ (w - 1) <= Zmod.signed x /\ Zmod.signed x + B < 2 ^ (w - 1).

  Lemma pow_w : 2 ^ w = 2 * 2 ^ (w - 1).
  Proof. rewrite <- Z.pow_succ_r by lia; f_equal; lia. Qed.

  Lemma signed_of_Z_small : forall z, - 2 ^ (w - 1) <= z < 2 ^ (w - 1) -> Zmod.signed (Zmod.of_Z (2 ^ w) z) = z.
  Proof.
    intros z Hz; rewrite Zmod.signed_of_Z; apply Z.smod_pow2_small; [lia |]; pose proof pow_w; lia.
  Qed.

  Lemma signed_shift : forall x, InRange x -> Zmod.signed (shiftV x) = Zmod.signed x + B.
  Proof.
    intros x [H1 H2]; unfold shiftV.
    rewrite Zmod.signed_add, signed_of_Z_small by lia.
    apply Z.smod_pow2_small; [lia |]; pose proof pow_w; lia.
  Qed.

  Lemma shift_sub : forall x y, Zmod.sub (shiftV x) (shiftV y) = Zmod.sub x y.
  Proof.
    intros x y; unfold shiftV; ring.
  Qed.

  Lemma shift_sub_r : forall x y, Zmod.sub (shiftV x) y = shiftV (Zmod.sub x y).
  Proof.
    intros x y; unfold shiftV; ring.
  Qed.

  Lemma shift_inj : forall x y, shiftV x = shiftV y -> x = y.
  Proof.
    intros x y H; pose proof (f_equal (fun v => Zmod.sub v (Zmod.of_Z _ B)) H) as H'; cbv beta in H'.
    unfold shiftV in H'.
    replace x with (Zmod.sub (Zmod.add x (Zmod.of_Z (2 ^ w) B)) (Zmod.of_Z (2 ^ w) B)) by ring.
    rewrite H'; ring.
  Qed.

  Lemma shift_eqb : forall x y, Zmod.eqb (shiftV x) (shiftV y) = Zmod.eqb x y.
  Proof.
    intros x y; destruct (Zmod.eqb_spec x y) as [-> | Hne]; [apply Zmod.eqb_refl |].
    destruct (Zmod.eqb_spec (shiftV x) (shiftV y)) as [He | _]; [exfalso; exact (Hne (shift_inj _ _ He)) | reflexivity].
  Qed.

  Lemma slt_shift : forall x y, InRange x -> InRange y ->
    Z.ltb (Zmod.signed (shiftV x)) (Zmod.signed (shiftV y)) = Z.ltb (Zmod.signed x) (Zmod.signed y).
  Proof.
    intros x y Hx Hy; rewrite !signed_shift by assumption.
    destruct (Z.ltb_spec (Zmod.signed x + B) (Zmod.signed y + B)); destruct (Z.ltb_spec (Zmod.signed x) (Zmod.signed y)); lia.
  Qed.

  (* Constants: the shifted constant is the constant plus the offset. *)
  Lemma shift_of_Z : forall c, shiftV (Zmod.of_Z _ c) = Zmod.of_Z _ (c + B).
  Proof.
    intros c; unfold shiftV; apply Zmod.unsigned_inj.
    rewrite Zmod.unsigned_add, !Zmod.unsigned_of_Z, Zplus_mod_idemp_l, Zplus_mod_idemp_r; reflexivity.
  Qed.

  Lemma InRange_of_Z : forall c, - 2 ^ (w - 1) <= c -> c + B < 2 ^ (w - 1) -> InRange (Zmod.of_Z _ c).
  Proof. intros c H1 H2; unfold InRange; rewrite signed_of_Z_small by lia; lia. Qed.
End Shift.
