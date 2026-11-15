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
 * `FpCore.roundPack` (reference mode) as integer arithmetic (`RoundBits.v`).
 *
 * `roundPack_Z`: the bits produced by `roundPack false` are those of the integer model `rpRes`,
 * `rpOvf`, `rpUf`, `rpNx` below (exponent `X = signed x`, significand `S = unsigned sigR`).  No
 * hypothesis on `X` or `S` is needed: the exponent arithmetic never wraps in `e + 3` bits.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift FpCoreRefProof IntMulProof.
From Fpu.FlocqProof Require Import Flags.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------
 * Bit-vector helpers
 * --------------------------------------------------------------------------- *)

Lemma tz_ofZ : forall w z, 0 <= w -> 0 <= z < 2 ^ w -> Zmod.to_Z (Zmod.of_Z (2 ^ w) z) = z.
Proof. intros w z Hw Hz; rewrite Zmod.unsigned_of_Z; apply Z.mod_small; exact Hz. Qed.

Lemma tz_sru : forall w (a : bits w) n, 0 <= w -> 0 <= n ->
  Zmod.to_Z (Zmod.sru a n) = Zmod.to_Z a / 2 ^ n.
Proof.
  intros w a n Hw Hn; unfold Zmod.sru; rewrite Zmod.unsigned_of_Z, Z.shiftr_div_pow2 by lia.
  pose proof (bits.unsigned_range a Hw).
  assert (H1 : 1 <= 2 ^ n) by (pose proof (Z.pow_pos_nonneg 2 n); lia).
  assert (H2 : Zmod.to_Z a / 2 ^ n <= Zmod.to_Z a) by (apply Z.div_le_upper_bound; nia).
  apply Z.mod_small; split; [apply Z.div_pos; lia | lia].
Qed.

(* `not (-1 << k)` keeps the low `k` bits. *)
Lemma tz_lowmask : forall w (a : bits w) k, 0 <= k <= w ->
  Zmod.to_Z (Zmod.and a (Zmod.not (Zmod.slu (Zmod.of_Z (2 ^ w) (-1)) k))) = Zmod.to_Z a mod 2 ^ k.
Proof.
  intros w a k Hk.
  rewrite bits.unsigned_and, bits.unsigned_not, bits.unsigned_slu, <- (Z.land_ones (Zmod.to_Z a) k) by lia.
  apply f_equal. apply Z.bits_inj'; intros i Hi.
  assert (Hm : -1 mod 2 ^ w = Z.ones w)
    by (rewrite Z.ones_equiv; symmetry; apply Z.mod_unique with (-1); pose proof (Z.pow_pos_nonneg 2 w); lia).
  rewrite Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i w) as [Hiw | Hiw].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite Zmod.unsigned_of_Z.
    destruct (Z.ltb_spec i k) as [Hik | Hik].
    + rewrite Z.shiftl_spec_low by lia; reflexivity.
    + rewrite Z.shiftl_spec by lia.
      rewrite Hm, Z.testbit_ones_nonneg by lia.
      destruct (Z.ltb_spec (i - k) w); [reflexivity | lia].
  - destruct (Z.ltb_spec i k); [lia | reflexivity].
Qed.

Lemma eqb_ofZ : forall w (a : bits w) k, 0 <= w -> 0 <= k < 2 ^ w ->
  Zmod.eqb a (Zmod.of_Z (2 ^ w) k) = (Zmod.to_Z a =? k).
Proof.
  intros w a k Hw Hk.
  destruct (Zmod.eqb_spec a (Zmod.of_Z (2 ^ w) k)) as [-> | Hn].
  - rewrite tz_ofZ by lia; symmetry; apply Z.eqb_refl.
  - symmetry; apply Z.eqb_neq; intros E; apply Hn, Zmod.unsigned_inj; rewrite tz_ofZ by lia; exact E.
Qed.

(* ---------------------------------------------------------------------------
 * Rounding decisions
 * --------------------------------------------------------------------------- *)

Definition rneZ (rmz : Z) : bool := (rmz =? 0) || negb (rmz <? 5).

(* `FpCore.roundInc` on the integer rounding mode. *)
Definition rmInc (rmz : Z) (s lsb g r : bool) : bool :=
  (rneZ rmz && g && (r || lsb)) || ((rmz =? 2) && (g || r) && s) ||
  ((rmz =? 3) && (g || r) && negb s) || ((rmz =? 4) && g).

Definition rmToInf (rmz : Z) (s : bool) : bool :=
  rneZ rmz || (rmz =? 4) || ((rmz =? 2) && s) || ((rmz =? 3) && negb s).

Lemma roundInc_eval : forall rm s lsb g r,
  evalExpr (roundInc type rm s lsb g r) = rmInc (Zmod.to_Z rm) s lsb g r.
Proof.
  intros rm s lsb g r; unfold roundInc, isRne, rmInc, rneZ, cst, RmRne, RmRdn, RmRup, RmRmm.
  cbn [evalExpr fold_left map evalOrBinary evalAndBinary evalBinary evalNot isEq KindCustomInd getDefault InvDefault].
  rewrite !(eqb_ofZ 3) by lia. change (Zmod.to_Z (Zmod.of_Z (2 ^ 3) 5)) with 5.
  destruct s, lsb, g, r; cbn [orb andb negb]; try reflexivity;
    destruct (Zmod.to_Z rm =? 0), (Zmod.to_Z rm <? 5), (Zmod.to_Z rm =? 2), (Zmod.to_Z rm =? 3), (Zmod.to_Z rm =? 4);
    reflexivity.
Qed.

Lemma overflowToInf_eval : forall rm s,
  evalExpr (overflowToInf type rm s) = rmToInf (Zmod.to_Z rm) s.
Proof.
  intros rm s; unfold overflowToInf, isRne, rmToInf, rneZ, cst, RmRne, RmRdn, RmRup, RmRmm.
  cbn [evalExpr fold_left map evalOrBinary evalAndBinary evalBinary evalNot isEq KindCustomInd getDefault InvDefault].
  rewrite !(eqb_ofZ 3) by lia. change (Zmod.to_Z (Zmod.of_Z (2 ^ 3) 5)) with 5.
  destruct s; cbn [orb andb negb];
    destruct (Zmod.to_Z rm =? 0), (Zmod.to_Z rm <? 5), (Zmod.to_Z rm =? 2), (Zmod.to_Z rm =? 3), (Zmod.to_Z rm =? 4);
    reflexivity.
Qed.

(* ---------------------------------------------------------------------------
 * `roundPack false`, transcribed
 * --------------------------------------------------------------------------- *)

Section RoundPack.
  Variable e f : Z.
  Hypothesis He : 2 <= e.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation XK := (Bit (e + 3)).

  (* `roundPack false` with its `LetE`s as Gallina `let`s (equal by conversion). *)
  Definition rpV (s : bool) (x : bits (e + 3)) (sigR : bits (f + 3)) (st : bool) (rm : bits 3) : type (FpOutK e f) :=
    let xe := rpExpV e f false x in
    let tinyPre := xe.(Fst) in
    let sh := xe.(Snd).(Fst) in
    let sigS := evalExpr (Srl (Var type (Bit (f + 3)) sigR) (Var type XK sh)) in
    let lostMask := evalExpr (Not (Sll (cst (f + 3) (-1)) (Var type XK sh))) in
    let stS := evalExpr (Or [ Var type Bool st ;
                              isNotZero (And [ Var type (Bit (f + 3)) sigR ; Var type (Bit (f + 3)) lostMask ]) ]) in
    let lsb := evalExpr (bitSet (ty := type) sigS 2) in
    let g := evalExpr (bitSet (ty := type) sigS 1) in
    let r := evalExpr (Or [ bitSet (ty := type) sigS 0 ; Var type Bool stS ]) in
    let inc := evalExpr (roundInc type rm s lsb g r) in
    let inexact := evalExpr (Or [ Var type Bool g ; Var type Bool r ]) in
    let kept := evalExpr (Srl (Var type (Bit (f + 3)) sigS) (cst (f + 3) 2)) in
    let rounded := evalExpr (Add [ Var type (Bit (f + 3)) kept ;
                                   ITE (Var type Bool inc) (cst (f + 3) 1) (cst (f + 3) 0) ]) in
    let bm1 := xe.(Snd).(Snd).(Fst) in
    let magW := evalExpr (Add [ Sll (zext (e + 3) (f + (e + 3)) (Var type XK bm1)) (cst (e + 3) f) ;
                                zext (f + 3) (f + (e + 3)) (Var type (Bit (f + 3)) rounded) ]) in
    let ovf := evalExpr (Or [ Var type Bool xe.(Snd).(Snd).(Snd).(Fst) ;
                              Not (Ult (Var type (Bit (f + (e + 3))) magW) (cst (f + (e + 3)) (infMagZ e f))) ]) in
    let toInf := evalExpr (overflowToInf type rm s) in
    let magOv := evalExpr (ITE (Var type Bool toInf) (cst (f + e) (infMagZ e f)) (cst (f + e) (infMagZ e f - 1))) in
    let magFin := evalExpr (ITE (Var type Bool ovf) (Var type (Bit (f + e)) magOv)
                                (trunc (f + (e + 3)) (f + e) (Var type (Bit (f + (e + 3))) magW))) in
    let lsb0 := evalExpr (bitSet (ty := type) sigR 2) in
    let g0 := evalExpr (bitSet (ty := type) sigR 1) in
    let r0 := evalExpr (Or [ bitSet (ty := type) sigR 0 ; Var type Bool st ]) in
    let inc0 := evalExpr (roundInc type rm s lsb0 g0 r0) in
    let kept0 := evalExpr (Srl (Var type (Bit (f + 3)) sigR) (cst (f + 3) 2)) in
    let carry0 := evalExpr (And [ Var type Bool inc0 ;
                                  Eq (Var type (Bit (f + 3)) kept0) (cst (f + 3) (2 ^ (f + 1) - 1)) ]) in
    let tiny := evalExpr (And [ Var type Bool tinyPre ;
                                Not (And [ Var type Bool xe.(Snd).(Snd).(Snd).(Snd).(Fst) ; Var type Bool carry0 ]) ]) in
    let uf := evalExpr (And [ Var type Bool tiny ; Var type Bool inexact ; Not (Var type Bool ovf) ]) in
    let nx := evalExpr (Or [ Var type Bool inexact ; Var type Bool ovf ]) in
    evalExpr (mkOut e f type (packSigned e f type (Var type Bool s) (Var type (Bit (f + e)) magFin))
                    (mkFlags type (ConstBool false) (ConstBool false) (Var type Bool ovf) (Var type Bool uf) (Var type Bool nx))).

  Lemma rp_eval : forall s x sigR st rm,
    evalLetExpr (roundPack false e f type s x sigR st rm) = rpV s x sigR st rm.
  Proof.
    intros s x sigR st rm; unfold roundPack; cbn [evalLetExpr]; rewrite (rpExp_eval e f He); exact eq_refl.
  Qed.

  (* ---------------------------------------------------------------------------
   * The integer model: exponent `X`, significand `S` (bit `f + 2` of weight 2^X), sticky `st`.
   * --------------------------------------------------------------------------- *)

  Definition rpTiny (X : Z) : bool := X <? fpEmin e.
  Definition rpSh (X : Z) : Z := if rpTiny X then Z.min (fpEmin e - X) (f + 3) else 0.
  Definition rpXEff (X : Z) : Z := if rpTiny X then fpEmin e else X.
  Definition rpSigS (X S : Z) : Z := S / 2 ^ rpSh X.
  Definition rpStS (X S : Z) (st : bool) : bool := st || negb (S mod 2 ^ rpSh X =? 0).
  Definition rpG (X S : Z) : bool := Z.testbit (rpSigS X S) 1.
  Definition rpR (X S : Z) (st : bool) : bool := Z.testbit (rpSigS X S) 0 || rpStS X S st.
  Definition rpInc (rmz : Z) (s : bool) (X S : Z) (st : bool) : bool :=
    rmInc rmz s (Z.testbit (rpSigS X S) 2) (rpG X S) (rpR X S st).
  Definition rpRnd (rmz : Z) (s : bool) (X S : Z) (st : bool) : Z :=
    rpSigS X S / 4 + b2z (rpInc rmz s X S st).
  Definition rpMagW (rmz : Z) (s : bool) (X S : Z) (st : bool) : Z :=
    (rpXEff X + fpBias e - 1) * 2 ^ f + rpRnd rmz s X S st.
  Definition rpOvf (rmz : Z) (s : bool) (X S : Z) (st : bool) : bool :=
    (fpEmax e <? X) || (infMagZ e f <=? rpMagW rmz s X S st).
  Definition rpMag (rmz : Z) (s : bool) (X S : Z) (st : bool) : Z :=
    if rpOvf rmz s X S st then (if rmToInf rmz s then infMagZ e f else infMagZ e f - 1)
    else rpMagW rmz s X S st.
  Definition rpRes (rmz : Z) (s : bool) (X S : Z) (st : bool) : Z :=
    b2z s * 2 ^ (f + e) + rpMag rmz s X S st.
  Definition rpCarry0 (rmz : Z) (s : bool) (S : Z) (st : bool) : bool :=
    rmInc rmz s (Z.testbit S 2) (Z.testbit S 1) (Z.testbit S 0 || st) && (S / 4 =? 2 ^ (f + 1) - 1).
  Definition rpInexact (X S : Z) (st : bool) : bool := rpG X S || rpR X S st.
  Definition rpUf (rmz : Z) (s : bool) (X S : Z) (st : bool) : bool :=
    (rpTiny X && negb ((X =? fpEmin e - 1) && rpCarry0 rmz s S st)) && rpInexact X S st &&
    negb (rpOvf rmz s X S st).
  Definition rpNx (rmz : Z) (s : bool) (X S : Z) (st : bool) : bool :=
    rpInexact X S st || rpOvf rmz s X S st.

  Lemma pow_e3 : 2 ^ (e + 3) = 16 * 2 ^ (e - 1).
  Proof. replace (e + 3) with ((e - 1) + 4) by lia; rewrite Z.pow_add_r by lia; lia. Qed.

  Lemma signed_k : forall k, - 8 * 2 ^ (e - 1) <= k < 8 * 2 ^ (e - 1) ->
    Zmod.signed (Zmod.of_Z (2 ^ (e + 3)) k) = k.
  Proof.
    intros k Hk; apply signed_of_Z_small; [lia |].
    replace (e + 3 - 1) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia.
  Qed.

  Lemma rpExpV_vals : forall x : bits (e + 3),
    let X := Zmod.signed x in
    (rpExpV e f false x).(Fst) = rpTiny X /\
    (rpExpV e f false x).(Snd).(Fst) = Zmod.of_Z _ (rpSh X) /\
    (rpExpV e f false x).(Snd).(Snd).(Fst) = Zmod.of_Z _ (rpXEff X + fpBias e - 1) /\
    (rpExpV e f false x).(Snd).(Snd).(Snd).(Fst) = (fpEmax e <? X) /\
    (rpExpV e f false x).(Snd).(Snd).(Snd).(Snd).(Fst) = (X =? fpEmin e - 1).
  Proof.
    intros x X.
    assert (Hp : 1 <= 2 ^ (e - 1)) by (pose proof (Z.pow_le_mono_r 2 0 (e - 1)); lia).
    pose proof (bits.signed_range' x ltac:(lia)) as HX; fold X in HX.
    assert (HXd : Zmod.signed x = X) by reflexivity; clearbody X.
    replace (e + 3 - 1) with ((e - 1) + 3) in HX by lia; rewrite Z.pow_add_r in HX by lia; change (2 ^ 3) with 8 in HX.
    unfold rpExpV, expOff, rpSh, rpXEff, rpTiny, fpEmin, fpEmax, fpBias in *; cbn [Fst Snd]; rewrite !Z.add_0_r, !Z.sub_0_r.
    rewrite signed_k by lia; rewrite HXd.
    split; [reflexivity |]; split; [| split; [| split]].
    - destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))) as [Ht | Ht]; [| reflexivity].
      assert (Hx : x = Zmod.of_Z _ X) by (rewrite <- HXd; symmetry; apply Zmod.of_Z_signed).
      assert (H1 : 0 <= 1 - (2 ^ (e - 1) - 1) - X < 2 ^ (e + 3)) by (rewrite pow_e3; lia).
      assert (H2 : 0 <= f + 3 < 2 ^ (e + 3)) by (rewrite pow_e3; lia).
      rewrite Hx, <- Zmod.of_Z_sub, (tz_ofZ (e + 3) _ ltac:(lia) H1), (tz_ofZ (e + 3) _ ltac:(lia) H2).
      destruct (Z.ltb_spec (1 - (2 ^ (e - 1) - 1) - X) (f + 3)); f_equal; lia.
    - assert (Hx : x = Zmod.of_Z _ X) by (rewrite <- HXd; symmetry; apply Zmod.of_Z_signed).
      rewrite Hx, Zmod.add_0_l; destruct (X <? 1 - (2 ^ (e - 1) - 1)); rewrite <- Zmod.of_Z_add; f_equal; lia.
    - rewrite slt_eval by lia; cbn [evalExpr cst]; rewrite signed_k by lia; rewrite HXd; reflexivity.
    - destruct (Zmod.eqb_spec x (Zmod.of_Z (2 ^ (e + 3)) (1 - (2 ^ (e - 1) - 1) - 1))) as [Hq | Hq];
        destruct (Z.eqb_spec X (1 - (2 ^ (e - 1) - 1) - 1)) as [Hz | Hz]; try reflexivity; exfalso.
      + apply Hz; rewrite <- HXd, Hq; apply signed_k; lia.
      + apply Hq, Zmod.signed_inj; rewrite signed_k by lia; rewrite HXd; exact Hz.
  Qed.

  Lemma rpSh_range : forall X, 0 <= rpSh X <= f + 3.
  Proof. intros X; unfold rpSh; destruct (rpTiny X) eqn:Ht; [unfold rpTiny in Ht; apply Z.ltb_lt in Ht; lia | lia]. Qed.

  Lemma pf3 : 2 ^ (f + 3) = 8 * 2 ^ f.
  Proof. rewrite Z.pow_add_r by lia; change (2 ^ 3) with 8; lia. Qed.

  Lemma pf1 : 2 ^ (f + 1) = 2 * 2 ^ f.
  Proof. rewrite Z.pow_add_r by lia; lia. Qed.

  Lemma sigS_bound : forall X S, 0 <= S < 2 ^ (f + 3) -> 0 <= rpSigS X S <= S.
  Proof.
    intros X S HS; unfold rpSigS; pose proof (rpSh_range X).
    assert (1 <= 2 ^ rpSh X) by (pose proof (Z.pow_le_mono_r 2 0 (rpSh X)); lia).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia].
  Qed.

  Lemma rnd_bound : forall rmz s X S st, 0 <= S < 2 ^ (f + 3) ->
    0 <= rpRnd rmz s X S st <= 2 ^ (f + 1).
  Proof.
    intros rmz s X S st HS; unfold rpRnd; pose proof (sigS_bound X S HS); rewrite pf3 in HS; rewrite pf1.
    assert (rpSigS X S / 4 < 2 * 2 ^ f) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= rpSigS X S / 4) by (apply Z.div_pos; lia).
    destruct (rpInc rmz s X S st); cbn [b2z]; lia.
  Qed.

  Theorem roundPack_Z : forall s x sigR st rm,
    let X := Zmod.signed x in let S := Zmod.to_Z sigR in let rmz := Zmod.to_Z rm in
    evalLetExpr (roundPack false e f type s x sigR st rm) =
    (Zmod.of_Z _ (rpRes rmz s X S st) ,,
     (mkFl false false (rpOvf rmz s X S st) (rpUf rmz s X S st) (rpNx rmz s X S st) ,, tt)).
  Proof.
    intros s x sigR st rm X S rmz.
    assert (HXd : Zmod.signed x = X) by reflexivity; assert (HSd : Zmod.to_Z sigR = S) by reflexivity;
      assert (Hrd : Zmod.to_Z rm = rmz) by reflexivity; clearbody X S rmz.
    assert (He3 : 0 <= f + 3 < 2 ^ (e + 3)) by (rewrite pow_e3; lia).
    pose proof (rpSh_range X) as Hsh.
    destruct (rpExpV_vals x) as (V1 & V2 & V3 & V4 & V5); rewrite HXd in V1, V2, V3, V4, V5.
    rewrite rp_eval; unfold rpV; cbv zeta; rewrite V1, V2, V3, V4, V5; clear V1 V2 V3 V4 V5.
    (* the shifted significand *)
    match goal with |- context [evalExpr (Srl (Var _ _ sigR) ?b)] => set (sigS := evalExpr (Srl (Var _ _ sigR) b)) end.
    assert (HsigS : Zmod.to_Z sigS = rpSigS X S).
    { unfold sigS; cbn [evalExpr]; rewrite (tz_ofZ (e + 3)) by lia; rewrite tz_sru by lia; rewrite HSd; reflexivity. }
    clearbody sigS.
    match goal with |- context [evalExpr (Or [Var _ _ st; ?t])] => set (stS := evalExpr (Or [Var _ _ st; t])) end.
    assert (HstS : stS = rpStS X S st).
    { unfold stS. cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
      rewrite evalExpr_isNotZero_bits.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd evalNot cst].
      rewrite unsigned_and_m1_l by lia. rewrite (tz_ofZ (e + 3)) by lia. rewrite tz_lowmask by lia.
      rewrite HSd; reflexivity. }
    clearbody stS.
    unfold mkOut, packSigned, mkFlags, boolBit.
    cbn [evalExpr fold_left map evalOrBinary evalAndBinary evalXorBinary evalBinary evalNot isEq KindCustomInd getDefault InvDefault mapDiffTuple].
    rewrite !bitSet_testbit by lia. rewrite !roundInc_eval, overflowToInf_eval, HsigS, HSd, HstS, Hrd.
    rewrite !orb_false_l, !andb_true_l.
    change (Z.testbit (rpSigS X S) 1) with (rpG X S).
    change (Z.testbit (rpSigS X S) 0 || rpStS X S st) with (rpR X S st).
    change (rmInc rmz s (Z.testbit (rpSigS X S) 2) (rpG X S) (rpR X S st)) with (rpInc rmz s X S st).
    change (rpG X S || rpR X S st) with (rpInexact X S st).
    (* constants *)
    pose proof (bits.unsigned_range sigR ltac:(lia)) as HSr; rewrite HSd in HSr.
    assert (Hc2 : Zmod.to_Z (evalExpr (cst (f + 3) 2)) = 2).
    { cbn [evalExpr cst]; apply tz_ofZ; [lia |]. split; [lia |]. apply Z.lt_le_trans with (2 ^ 2); [cbn; lia | apply Z.pow_le_mono_r; lia]. }
    rewrite Hc2.
    (* the rounded significand *)
    match goal with |- context [Zmod.add (Zmod.add Zmod.zero (Zmod.sru sigS 2)) ?t] =>
      set (rnd := Zmod.add (Zmod.add Zmod.zero (Zmod.sru sigS 2)) t) end.
    assert (Hrnd : Zmod.to_Z rnd = rpRnd rmz s X S st).
    { unfold rnd. pose proof (rnd_bound rmz s X S st HSr) as Hb; unfold rpRnd in *.
      pose proof (sigS_bound X S HSr).
      rewrite !Zmod.unsigned_add, Zmod.unsigned_0, tz_sru by lia. rewrite HsigS. change (2 ^ 2) with 4.
      assert (Hp : 2 ^ (f + 1) < 2 ^ (f + 3)) by (rewrite pf1, pf3; lia).
      assert (H2f : 4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
      pose proof pf1; pose proof pf3.
      assert (0 <= rpSigS X S / 4 < 2 * 2 ^ f) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite Z.add_0_l, (Z.mod_small (rpSigS X S / 4)) by lia.
      destruct (rpInc rmz s X S st); cbn [evalExpr cst b2z] in *; rewrite tz_ofZ by lia;
        rewrite Z.mod_small by lia; lia. }
    clearbody rnd.
    (* the packed magnitude *)
    pose proof (bits.signed_range' x ltac:(lia)) as HX; rewrite HXd in HX.
    replace (e + 3 - 1) with ((e - 1) + 3) in HX by lia; rewrite Z.pow_add_r in HX by lia; change (2 ^ 3) with 8 in HX.
    assert (Hp : 1 <= 2 ^ (e - 1)) by (pose proof (Z.pow_le_mono_r 2 0 (e - 1)); lia).
    pose proof pow_e3 as E3; pose proof pf1 as F1; pose proof pf3 as F3.
    assert (Hfe3 : 2 ^ (f + (e + 3)) = 2 ^ f * 2 ^ (e + 3)) by (apply Z.pow_add_r; lia); rewrite E3 in Hfe3.
    assert (H2f : 4 <= 2 ^ f) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (Hxe : 0 <= rpXEff X + fpBias e - 1 <= 9 * 2 ^ (e - 1) - 3).
    { unfold rpXEff, rpTiny, fpEmin, fpBias; destruct (Z.ltb_spec X (1 - (2 ^ (e - 1) - 1))); lia. }
    pose proof (rnd_bound rmz s X S st HSr) as Hrb.
    assert (HA : 0 <= (rpXEff X + fpBias e - 1) * 2 ^ f <= (9 * 2 ^ (e - 1) - 3) * 2 ^ f)
      by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg_r]; lia).
    assert (Hmw : 0 <= rpMagW rmz s X S st < 2 ^ f * (9 * 2 ^ (e - 1))) by (unfold rpMagW; lia).
    match goal with |- context [Zmod.add (Zmod.add Zmod.zero (Zmod.slu ?a ?b)) ?c] =>
      set (magW := Zmod.add (Zmod.add Zmod.zero (Zmod.slu a b)) c) end.
    assert (HmagW : Zmod.to_Z magW = rpMagW rmz s X S st).
    { unfold magW; rewrite !Zmod.unsigned_add, Zmod.unsigned_0, Z.add_0_l, bits.unsigned_slu.
      rewrite !unsigned_zext by lia; cbn [evalExpr cst]. rewrite !tz_ofZ by lia. rewrite Hrnd, Z.shiftl_mul_pow2 by lia.
      unfold rpMagW; rewrite (Z.mod_small ((rpXEff X + fpBias e - 1) * 2 ^ f)) by lia; rewrite (Z.mod_small ((rpXEff X + fpBias e - 1) * 2 ^ f)) by lia; rewrite Z.mod_small; lia. }
    clearbody magW.
    assert (Hinf : Zmod.to_Z (evalExpr (cst (f + (e + 3)) (infMagZ e f))) = infMagZ e f).
    { cbn [evalExpr cst]; apply tz_ofZ; [lia |]. unfold infMagZ.
      assert (2 ^ e = 2 * 2 ^ (e - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      rewrite H; nia. }
    rewrite Hinf, HmagW, <- Z.leb_antisym.
    change ((fpEmax e <? X) || (infMagZ e f <=? rpMagW rmz s X S st)) with (rpOvf rmz s X S st).
    assert (Hc0 : Zmod.eqb (Zmod.sru sigR 2) (evalExpr (cst (f + 3) (2 ^ (f + 1) - 1))) = (S / 4 =? 2 ^ (f + 1) - 1)).
    { cbn [evalExpr cst]; rewrite eqb_ofZ by lia; rewrite tz_sru by lia; rewrite HSd; reflexivity. }
    rewrite Hc0.
    change (rmInc rmz s (Z.testbit S 2) (Z.testbit S 1) (Z.testbit S 0 || st) && (S / 4 =? 2 ^ (f + 1) - 1))
      with (rpCarry0 rmz s S st).
    change ((rpTiny X && negb ((X =? fpEmin e - 1) && rpCarry0 rmz s S st)) && rpInexact X S st &&
            negb (rpOvf rmz s X S st)) with (rpUf rmz s X S st).
    change (rpInexact X S st || rpOvf rmz s X S st) with (rpNx rmz s X S st).
    assert (H2e : 2 ^ e = 2 * 2 ^ (e - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; lia).
    assert (Hinf2 : 0 < infMagZ e f < 2 ^ (f + e)) by (unfold infMagZ; rewrite Hfe, H2e; nia).
    assert (Hmag : 0 <= rpMag rmz s X S st < 2 ^ (f + e)).
    { unfold rpMag; destruct (rpOvf rmz s X S st) eqn:Ho; [destruct (rmToInf rmz s); lia |].
      unfold rpOvf in Ho; apply orb_false_iff in Ho as [_ Ho]; apply Z.leb_gt in Ho; lia. }
    f_equal; [| f_equal]; cbn [Fst Snd].
    - apply Zmod.unsigned_inj; cbn [snd evalExpr]. rewrite unsigned_app_arith by lia.
      assert (Hfe1 : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
      rewrite tz_ofZ by (unfold rpRes; destruct s; cbn [b2z]; lia).
      unfold rpRes.
      match goal with |- Zmod.unsigned ?A + Zmod.unsigned ?Bs * _ = _ =>
        assert (Hm : Zmod.unsigned A = rpMag rmz s X S st);
        [| assert (Hs : Zmod.unsigned Bs = b2z s) by (destruct s; reflexivity); rewrite Hm, Hs; lia] end.
      unfold rpMag in *; destruct (rpOvf rmz s X S st) eqn:Ho.
      + destruct (rmToInf rmz s); cbn [evalExpr cst]; apply tz_ofZ; lia.
      + rewrite unsigned_trunc by lia; cbn [evalExpr]; rewrite HmagW; apply Z.mod_small.
        unfold rpOvf in Ho; apply orb_false_iff in Ho as [_ Ho]; apply Z.leb_gt in Ho; lia.
    - cbn [snd]; unfold mkFl; destruct (rpOvf rmz s X S st), (rpUf rmz s X S st), (rpNx rmz s X S st); vm_compute; reflexivity.
  Qed.
End RoundPack.
