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
 * The FPU operations without a Flocq counterpart (`Misc.v`), specified with Flocq predicates on
 * `toB` / `toBp` plus the RISC-V rules, against the reference core (`FpCoreRef.fpuComputeRef`):
 * - `fcmp_flocq`: FEQ / FLT / FLE / FLTQ / FLEQ via `Bcompare`; NV per RISC-V;
 * - `fminmax_flocq`: FMIN / FMAX / FMINM / FMAXM via `Bcompare` / `Bsign` (`-0 < +0`); NV for sNaN;
 * - `fsgnj_bits` (bit level) and `fsgnj_flocq` (`a` or `Bopp a`, sign from `Bsign`);
 * - `fclass_flocq`: the 10-bit class mask from the shape of `toB a` and `isSNaN`;
 * - `fli_flocq` / `fli_canon`: every Zfa FLI table entry (`fliConstE`) decodes to its constant.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode Unpack Mul.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Section Misc.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).

  Definition mkOp (minmax sgnj cmp fclass isMax nanProp : bool) (md : bits 2) (quiet : bool) : type FpOpDK :=
    (false ,, (false ,, (false ,, (false ,, (false ,, (minmax ,, (sgnj ,, (cmp ,, (fclass ,,
    (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (isMax ,, (nanProp ,,
    (md ,, (quiet ,, (false ,, (false ,, (false ,, tt)))))))))))))))))))))).

  Definition miscRef (op : type FpOpDK) (rm : bits 3) (a b : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqOf e f xlen op rm a b Zmod.zero Zmod.zero)).

  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Abbreviation uSign := (fun (u : type (FpUnpK e f)) => u.(Fst)).
  Local Abbreviation uZero := (fun (u : type (FpUnpK e f)) => u.(Snd).(Fst)).
  Local Abbreviation uInf := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Fst)).
  Local Abbreviation uNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation uSNaN := (fun (u : type (FpUnpK e f)) => u.(Snd).(Snd).(Snd).(Snd).(Fst)).
  Local Abbreviation fl0 x := (evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) x)).

  Definition cmpV (md : bits 2) (q : bool) (a b : bits W) (ua ub : type (FpUnpK e f)) : type (IntOutK xlen) :=
    let sa := uSign ua in let sb := uSign ub in
    let ma := Zmod.firstn (f + e) a in let mb := Zmod.firstn (f + e) b in
    let anyNaN := uNaN ua || uNaN ub in
    let zz := uZero ua && uZero ub in
    let eq := negb anyNaN && (Zmod.eqb a b || zz) in
    let lt := negb anyNaN && negb zz && ((sa && negb sb) || (negb sa && negb sb && (Zmod.to_Z ma <? Zmod.to_Z mb)) ||
                                          (sa && sb && (Zmod.to_Z mb <? Zmod.to_Z ma))) in
    let isEqK := Zmod.eqb md (Zmod.of_Z _ 0) in
    let isLtK := Zmod.eqb md (Zmod.of_Z _ 1) in
    let res := if isEqK then eq else if isLtK then lt else lt || eq in
    let nv := if isEqK || q then uSNaN ua || uSNaN ub else anyNaN in
    ((if res then Zmod.of_Z _ 1 else Zmod.of_Z _ 0) ,, (evalExpr (nvFlag type (ConstBool nv)) ,, tt)).

  Lemma cmp_core : forall md q rm a b,
    (miscRef (mkOp false false true false false false md q) rm a b) @% "xres" = (cmpV md q a (fl0 b) (unp a) (unp (fl0 b))).(Fst) /\
    (miscRef (mkOp false false true false false false md q) rm a b) @% "flags" = (cmpV md q a (fl0 b) (unp a) (unp (fl0 b))).(Snd).(Fst).
  Proof. intros; split; exact eq_refl. Qed.

  Definition mmV (isMax nanP : bool) (a b : bits W) (ua ub : type (FpUnpK e f)) : type (FpOutK e f) :=
    let sa := uSign ua in let sb := uSign ub in
    let ma := Zmod.firstn (f + e) a in let mb := Zmod.firstn (f + e) b in
    let lt := (sa && negb sb) || (negb sa && negb sb && (Zmod.to_Z ma <? Zmod.to_Z mb)) ||
              (sa && sb && (Zmod.to_Z mb <? Zmod.to_Z ma)) in
    let pick := if evalExpr (Xor [Var type Bool lt; Var type Bool isMax]) then a else b in
    let nv := uSNaN ua || uSNaN ub in
    ((if (uNaN ua && uNaN ub) || (nanP && (uNaN ua || uNaN ub)) then evalExpr (qnanE e f type)
      else if uNaN ua then b else if uNaN ub then a else pick) ,,
     (evalExpr (mkFlags type (ConstBool nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt)).

  Lemma mm_core : forall isMax nanP rm a b,
    (miscRef (mkOp true false false false isMax nanP Zmod.zero false) rm a b) @% "res" = (mmV isMax nanP a (fl0 b) (unp a) (unp (fl0 b))).(Fst) /\
    (miscRef (mkOp true false false false isMax nanP Zmod.zero false) rm a b) @% "flags" = (mmV isMax nanP a (fl0 b) (unp a) (unp (fl0 b))).(Snd).(Fst).
  Proof. intros; split; exact eq_refl. Qed.

  Definition sjV (md : bits 2) (a b : bits W) : type (FpOutK e f) :=
    let sa := evalExpr (isNotZero (TruncMsb 1 (f + e) (Var type (Bit W) a))) in
    let sb := evalExpr (isNotZero (TruncMsb 1 (f + e) (Var type (Bit W) b))) in
    let s := if Zmod.eqb md (Zmod.of_Z _ 0) then sb else if Zmod.eqb md (Zmod.of_Z _ 1) then negb sb
             else evalExpr (Xor [Var type Bool sa; Var type Bool sb]) in
    (evalExpr (packSigned e f type (ConstBool s) (magOf e f type a)) ,, (evalExpr (noFlags type) ,, tt)).

  Lemma sj_core : forall md rm a b,
    (miscRef (mkOp false true false false false false md false) rm a b) @% "res" = (sjV md a (fl0 b)).(Fst) /\
    (miscRef (mkOp false true false false false false md false) rm a b) @% "flags" = (sjV md a (fl0 b)).(Snd).(Fst).
  Proof. intros; split; exact eq_refl. Qed.

  Definition clsV (a : bits W) (ua : type (FpUnpK e f)) : type (IntOutK xlen) :=
    let s := uSign ua in
    let ez := evalExpr (isZero (Var type (Bit e) (Zmod_lastn e (Zmod.firstn (f + e) a)))) in
    let sub := ez && negb (uZero ua) in
    let norm := negb ez && negb (uInf ua) && negb (uNaN ua) in
    let snan := uSNaN ua in
    let qnan := uNaN ua && negb snan in
    (evalExpr (Or [ ITE (ConstBool (s && uInf ua)) (cst xlen 1) (cst xlen 0) ;
                    ITE (ConstBool (s && norm)) (cst xlen 2) (cst xlen 0) ;
                    ITE (ConstBool (s && sub)) (cst xlen 4) (cst xlen 0) ;
                    ITE (ConstBool (s && uZero ua)) (cst xlen 8) (cst xlen 0) ;
                    ITE (ConstBool (negb s && uZero ua)) (cst xlen 16) (cst xlen 0) ;
                    ITE (ConstBool (negb s && sub)) (cst xlen 32) (cst xlen 0) ;
                    ITE (ConstBool (negb s && norm)) (cst xlen 64) (cst xlen 0) ;
                    ITE (ConstBool (negb s && uInf ua)) (cst xlen 128) (cst xlen 0) ;
                    ITE (ConstBool snan) (cst xlen 256) (cst xlen 0) ;
                    ITE (ConstBool qnan) (cst xlen 512) (cst xlen 0) ]) ,,
     (evalExpr (noFlags type) ,, tt)).

  Lemma cls_core : forall rm a b,
    (miscRef (mkOp false false false true false false Zmod.zero false) rm a b) @% "xres" = (clsV a (unp a)).(Fst) /\
    (miscRef (mkOp false false false true false false Zmod.zero false) rm a b) @% "flags" = (clsV a (unp a)).(Snd).(Fst).
  Proof. intros; split; exact eq_refl. Qed.

  (* ---------------------------------------------------------------------------
   * Generic helpers
   * --------------------------------------------------------------------------- *)

  Lemma zeqb : forall m (x y : Zmod m), Zmod.eqb x y = (Zmod.to_Z x =? Zmod.to_Z y).
  Proof.
    intros m x y; destruct (Zmod.eqb_spec x y) as [-> | Hn]; [symmetry; apply Z.eqb_refl |].
    symmetry; apply Z.eqb_neq; intros H; apply Hn, Zmod.unsigned_inj; exact H.
  Qed.

  Lemma eqb_md : forall (md : bits 2) k, 0 <= k < 4 -> Zmod.eqb md (Zmod.of_Z _ k) = (Zmod.to_Z md =? k).
  Proof. intros md k Hk; rewrite zeqb, Zmod.unsigned_of_Z, Z.mod_small by (cbn; lia); reflexivity. Qed.

  Lemma nvFlag_eval : forall nv, evalExpr (nvFlag type (ConstBool nv)) = mkFl nv false false false false.
  Proof. intros [|]; reflexivity. Qed.

  Lemma mkFlags_eval : forall nv,
    evalExpr (mkFlags type (ConstBool nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) = mkFl nv false false false false.
  Proof. intros [|]; reflexivity. Qed.

  Lemma noFlags_eval : evalExpr (noFlags type) = mkFl false false false false false.
  Proof. reflexivity. Qed.

  Lemma xor_eval : forall x y, evalExpr (Xor [Var type Bool x; Var type Bool y]) = xorb x y.
  Proof. intros [|] [|]; reflexivity. Qed.

  Local Abbreviation eminF := (SpecFloat.emin (f + 1) (2 ^ (e - 1))).

  (* Facts about the fields of a pattern. *)
  Section Fields.
    Variable x : bits W.
    Variables (s : bool) (E M : Z).
    Hypothesis HM : 0 <= M < 2 ^ f.
    Hypothesis HE : 0 <= E < 2 ^ e.
    Hypothesis Hx : Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M.

    Lemma nan_fields : BinarySingleNaN.is_nan (toB x) = (E =? 2 ^ e - 1) && negb (M =? 0).
    Proof.
      rewrite (is_nan_B2SF e f), (B2SF_toB_fields e f Hf Hpe x s E M HM HE Hx). unfold sfFields.
      destruct (Z.eqb_spec E 0); destruct (Z.eqb_spec M 0); destruct (Z.eqb_spec E (2 ^ e - 1)); try reflexivity.
      pose proof (HeM e f Hf Hpe). assert (4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia). lia.
    Qed.

  End Fields.

    Lemma zero_fields : forall E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e -> (E =? 0) && (M =? 0) = (E * 2 ^ f + M =? 0).
    Proof.
      intros E M HM HE.
      assert (H1 : 1 <= E -> 1 * 2 ^ f <= E * 2 ^ f) by (intros; apply Z.mul_le_mono_nonneg_r; lia).
      assert (0 <= E * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia). pose proof (Z.pow_pos_nonneg 2 f).
      destruct (Z.eqb_spec E 0); destruct (Z.eqb_spec M 0); destruct (Z.eqb_spec (E * 2 ^ f + M) 0); subst; try reflexivity; lia.
    Qed.

    Lemma mag_bound : forall E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e -> 0 <= E * 2 ^ f + M < 2 ^ (f + e).
    Proof.
      intros E M HM HE. pose proof (HeM e f Hf Hpe). rewrite Z.pow_add_r by lia.
      assert (E * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (0 <= E * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia). lia.
    Qed.

  (* ---------------------------------------------------------------------------
   * Comparison on the fields
   * --------------------------------------------------------------------------- *)

  (* The order of two non-NaN patterns from their signs and magnitudes (`-0 = +0`). *)
  Definition magCmp (s : bool) (A : Z) (s' : bool) (B : Z) : comparison :=
    if (A =? 0) && (B =? 0) then Datatypes.Eq else
    match s, s' with
    | false, false => Z.compare A B
    | true, true => Z.compare B A
    | true, false => Lt
    | false, true => Gt
    end.

  (* The shape of a non-NaN spec float with sign `s` and magnitude `A` (`E * 2^f + M`). *)
  Definition shp (x : spec_float) (s : bool) (A : Z) : Prop :=
    match x with
    | S754_zero s' => s' = s /\ A = 0
    | S754_infinity s' => s' = s /\ A = (2 ^ e - 1) * 2 ^ f
    | S754_nan => False
    | S754_finite s' m k =>
        s' = s /\ 0 < A < (2 ^ e - 1) * 2 ^ f /\ eminF <= k /\ Zpos m < 2 * 2 ^ f /\
        (eminF < k -> 2 ^ f <= Zpos m) /\ A = (k - eminF) * 2 ^ f + Zpos m
    end.

  Lemma shp_fields : forall s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e -> ~ (E = 2 ^ e - 1 /\ M <> 0) ->
    shp (sfFields e f s E M) s (E * 2 ^ f + M).
  Proof.
    intros s E M HM HE Hn. pose proof (HeM e f Hf Hpe). pose proof (Z.pow_pos_nonneg 2 f).
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (F1 : 1 <= E -> 1 * 2 ^ f <= E * 2 ^ f) by (intros; apply Z.mul_le_mono_nonneg_r; lia).
    assert (F2 : E <= 2 ^ e - 2 -> E * 2 ^ f <= (2 ^ e - 2) * 2 ^ f) by (intros; apply Z.mul_le_mono_nonneg_r; lia).
    assert (F3 : 1 * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia).
    unfold sfFields; destruct (Z.eqb_spec E 0); destruct (Z.eqb_spec M 0); try destruct (Z.eqb_spec E (2 ^ e - 1));
      cbn [shp]; subst; try rewrite Z2Pos.id by lia; repeat split; lia.
  Qed.

  Lemma lexP : forall k k' (m m' : positive) A B,
    (k < k' -> A < B) -> (k' < k -> B < A) -> (k = k' -> Zpos m - Zpos m' = A - B) ->
    match Z.compare k k' with Lt => Lt | Gt => Gt | Datatypes.Eq => Pos.compare_cont Datatypes.Eq m m' end = Z.compare A B.
  Proof.
    intros k k' m m' A B H1 H2 H3; destruct (Z.compare_spec k k') as [Hk | Hk | Hk].
    - specialize (H3 Hk). change (Pos.compare_cont Datatypes.Eq m m') with (Z.compare (Zpos m) (Zpos m')).
      rewrite Z.compare_sub, (Z.compare_sub A B), H3; reflexivity.
    - symmetry; apply Z.compare_lt_iff; auto.
    - symmetry; apply Z.compare_gt_iff; auto.
  Qed.

  Lemma lexN : forall k k' (m m' : positive) A B,
    (k < k' -> A < B) -> (k' < k -> B < A) -> (k = k' -> Zpos m - Zpos m' = A - B) ->
    match Z.compare k k' with Lt => Gt | Gt => Lt | Datatypes.Eq => CompOpp (Pos.compare_cont Datatypes.Eq m m') end = Z.compare B A.
  Proof.
    intros k k' m m' A B H1 H2 H3; destruct (Z.compare_spec k k') as [Hk | Hk | Hk].
    - specialize (H3 Hk). change (Pos.compare_cont Datatypes.Eq m m') with (Z.compare (Zpos m) (Zpos m')).
      rewrite <- Z.compare_antisym, Z.compare_sub, (Z.compare_sub B A).
      replace (Zpos m' - Zpos m) with (B - A) by lia; reflexivity.
    - symmetry; apply Z.compare_gt_iff; auto.
    - symmetry; apply Z.compare_lt_iff; auto.
  Qed.

  Lemma lex_side : forall k k' m m' A B,
    eminF <= k -> m < 2 * 2 ^ f -> (eminF < k' -> 2 ^ f <= m') ->
    A = (k - eminF) * 2 ^ f + m -> B = (k' - eminF) * 2 ^ f + m' -> k < k' -> A < B.
  Proof.
    intros k k' m m' A B Hk Hm Hm' -> -> Hlt.
    assert ((k - eminF + 1) * 2 ^ f <= (k' - eminF) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg |]; lia).
    specialize (Hm' ltac:(lia)). lia.
  Qed.

  Lemma cmp_shp : forall x y s A s' B, shp x s A -> shp y s' B -> SFcompare x y = Some (magCmp s A s' B).
  Proof.
    intros [s1 | s1 | | s1 m k] [s2 | s2 | | s2 m' k'] s A s' B Hx Hy; cbn [shp] in Hx, Hy; try contradiction;
      unfold magCmp; pose proof (Z.pow_pos_nonneg 2 f ltac:(lia));
      assert (F3 : 1 * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; [lia |];
        pose proof (HeM e f Hf Hpe); assert (4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia); lia);
      repeat match goal with H : _ /\ _ |- _ => destruct H end; subst s1 s2;
      destruct (Z.eqb_spec A 0); destruct (Z.eqb_spec B 0); cbn [andb]; try (exfalso; lia);
      destruct s, s'; cbn [SFcompare]; try reflexivity;
      try (f_equal; symmetry; first [apply Z.compare_lt_iff | apply Z.compare_gt_iff | apply Z.compare_eq_iff]; lia).
    all: f_equal; first [apply lexP | apply lexN];
      [ apply (lex_side k k' (Zpos m) (Zpos m') A B); assumption
      | apply (lex_side k' k (Zpos m') (Zpos m) B A); assumption
      | intros Hk; subst k'; lia ].
  Qed.

  Lemma bcmp_fields : forall a b sa Ea Ma sb Eb Mb,
    0 <= Ma < 2 ^ f -> 0 <= Ea < 2 ^ e -> Zmod.to_Z a = b2z sa * 2 ^ (f + e) + Ea * 2 ^ f + Ma ->
    0 <= Mb < 2 ^ f -> 0 <= Eb < 2 ^ e -> Zmod.to_Z b = b2z sb * 2 ^ (f + e) + Eb * 2 ^ f + Mb ->
    BinarySingleNaN.is_nan (toB a) = false -> BinarySingleNaN.is_nan (toB b) = false ->
    BinarySingleNaN.Bcompare (toB a) (toB b) = Some (magCmp sa (Ea * 2 ^ f + Ma) sb (Eb * 2 ^ f + Mb)).
  Proof.
    intros a b sa Ea Ma sb Eb Mb HMa HEa Ha HMb HEb Hb Hna Hnb.
    rewrite (nan_fields a sa Ea Ma HMa HEa Ha) in Hna. rewrite (nan_fields b sb Eb Mb HMb HEb Hb) in Hnb.
    unfold BinarySingleNaN.Bcompare. rewrite (B2SF_toB_fields e f Hf Hpe a sa Ea Ma HMa HEa Ha), (B2SF_toB_fields e f Hf Hpe b sb Eb Mb HMb HEb Hb).
    apply cmp_shp; apply shp_fields; try assumption.
    - intros [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_neq in H2; rewrite H1, H2 in Hna; discriminate.
    - intros [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_neq in H2; rewrite H1, H2 in Hnb; discriminate.
  Qed.

  Lemma bcmp_nan : forall x y, BinarySingleNaN.is_nan x || BinarySingleNaN.is_nan y = true ->
    BinarySingleNaN.Bcompare (prec := f + 1) (emax := 2 ^ (e - 1)) x y = None.
  Proof. intros [| | |] [| | |]; cbn; congruence. Qed.

  (* ---------------------------------------------------------------------------
   * 1. FEQ / FLT / FLE (mode 0 / 1 / 2; mode 3 behaves as FLE); Zfa FLTQ / FLEQ (quiet)
   * --------------------------------------------------------------------------- *)

  Ltac cmp_hyps :=
    repeat match goal with
    | H : (_ ?= _) = Datatypes.Eq |- _ => apply (proj1 (Z.compare_eq_iff _ _)) in H
    | H : (_ ?= _) = Datatypes.Lt |- _ => apply (proj1 (Z.compare_lt_iff _ _)) in H
    | H : (_ ?= _) = Datatypes.Gt |- _ => apply (proj1 (Z.compare_gt_iff _ _)) in H
    end.

  Lemma L_eq : forall s s' A B T X Y, X = b2z s * T + A -> Y = b2z s' * T + B -> 0 <= A < T -> 0 <= B < T ->
    (X =? Y) || ((A =? 0) && (B =? 0)) = match magCmp s A s' B with Datatypes.Eq => true | _ => false end.
  Proof.
    intros s s' A B T X Y -> -> HA HB; unfold magCmp.
    destruct (Z.eqb_spec A 0); destruct (Z.eqb_spec B 0); cbn [andb orb]; [rewrite orb_true_r; reflexivity | | |];
      rewrite orb_false_r; destruct s, s'; cbn [b2z];
      destruct (A ?= B) eqn:C1; destruct (B ?= A) eqn:C2; cmp_hyps;
      repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end; try reflexivity; lia.
  Qed.

  Lemma L_lt : forall s s' A B,
    negb ((A =? 0) && (B =? 0)) && ((s && negb s') || (negb s && negb s' && (A <? B)) || (s && s' && (B <? A))) =
    match magCmp s A s' B with Lt => true | _ => false end.
  Proof.
    intros s s' A B; unfold magCmp.
    destruct ((A =? 0) && (B =? 0)); [reflexivity |]; cbn [negb andb]. destruct s, s'; cbn [andb orb negb]; try reflexivity;
      destruct (A ?= B) eqn:C1; destruct (B ?= A) eqn:C2; cmp_hyps;
      repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end; try reflexivity; lia.
  Qed.

  (* The integer result: `Some Eq` for FEQ / FLE, `Some Lt` for FLT / FLE. *)
  Definition cmpBit (md : bits 2) (c : option comparison) : bool :=
    match c with
    | Some Datatypes.Eq => negb (Zmod.to_Z md =? 1)
    | Some Lt => negb (Zmod.to_Z md =? 0)
    | _ => false
    end.

  (* NV: FEQ and the quiet FLTQ / FLEQ only for a signaling NaN, FLT / FLE for any NaN. *)
  Definition cmpFlags (md : bits 2) (q : bool) (a b : bits W) : bits 5 :=
    mkFl (if (Zmod.to_Z md =? 0) || q then isSNaN e f Hf Hpe a || isSNaN e f Hf Hpe b
          else BinarySingleNaN.is_nan (toB a) || BinarySingleNaN.is_nan (toB b)) false false false false.

  Theorem fcmp_flocq : forall md q rm a b,
    (miscRef (mkOp false false true false false false md q) rm a b) @% "xres" =
      Zmod.of_Z _ (b2z (cmpBit md (BinarySingleNaN.Bcompare (toB a) (toB b)))) /\
    (miscRef (mkOp false false true false false false md q) rm a b) @% "flags" = cmpFlags md q a b.
  Proof.
    intros md q rm a b. destruct (cmp_core md q rm a b) as [-> ->]. rewrite (flip0 e f Hf Hpe b).
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    pose proof (HeM e f Hf Hpe) as He.
    unfold cmpV, cmpFlags; cbn [Fst Snd].
    rewrite (u_sign e f He Hf a sa Ea Ma HMa HEa Ha), (u_sign e f He Hf b sb Eb Mb HMb HEb Hb),
      (u_zero e f He Hf a sa Ea Ma HMa HEa Ha), (u_zero e f He Hf b sb Eb Mb HMb HEb Hb),
      (u_nan e f He Hf a sa Ea Ma HMa HEa Ha), (u_nan e f He Hf b sb Eb Mb HMb HEb Hb),
      (u_snan e f He Hf a sa Ea Ma HMa HEa Ha), (u_snan e f He Hf b sb Eb Mb HMb HEb Hb),
      (Hmag e f He Hf a sa Ea Ma HMa HEa Ha), (Hmag e f He Hf b sb Eb Mb HMb HEb Hb),
      !eqb_md, zeqb, nvFlag_eval by lia.
    rewrite (isSNaN_eq e f Hf Hpe a sa Ea Ma HMa HEa Ha), (isSNaN_eq e f Hf Hpe b sb Eb Mb HMb HEb Hb),
      <- (nan_fields a sa Ea Ma HMa HEa Ha), <- (nan_fields b sb Eb Mb HMb HEb Hb),
      (zero_fields Ea Ma HMa HEa), (zero_fields Eb Mb HMb HEb).
    split; [| reflexivity].
    destruct (BinarySingleNaN.is_nan (toB a)) eqn:NA; destruct (BinarySingleNaN.is_nan (toB b)) eqn:NB.
    1-3: rewrite bcmp_nan by (rewrite NA, NB; reflexivity); cbn [negb andb orb cmpBit b2z];
      destruct (Zmod.to_Z md =? 0), (Zmod.to_Z md =? 1); reflexivity.
    rewrite (bcmp_fields a b sa Ea Ma sb Eb Mb HMa HEa Ha HMb HEb Hb NA NB).
    cbn [negb andb orb].
    rewrite (L_eq sa sb (Ea * 2 ^ f + Ma) (Eb * 2 ^ f + Mb) (2 ^ (f + e)) (Zmod.to_Z a) (Zmod.to_Z b) ltac:(rewrite Ha; ring) ltac:(rewrite Hb; ring)
      (mag_bound Ea Ma HMa HEa) (mag_bound Eb Mb HMb HEb)), L_lt.
    unfold cmpBit; destruct (magCmp _ _ _ _); destruct (Z.eqb_spec (Zmod.to_Z md) 0); destruct (Z.eqb_spec (Zmod.to_Z md) 1);
      cbn [andb orb negb b2z]; first [reflexivity | lia].
  Qed.
  (* ---------------------------------------------------------------------------
   * 2. FMIN / FMAX (isMax); Zfa FMINM / FMAXM (nanProp)
   * --------------------------------------------------------------------------- *)

  Lemma sign_fields : forall x s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    BinarySingleNaN.is_nan (toB x) = false -> BinarySingleNaN.Bsign (toB x) = s.
  Proof.
    intros x s E M HM HE Hx Hn. pose proof (cls e f Hf Hpe x s E M HM HE Hx) as C.
    destruct (toB x); cbn [clsP] in C; cbn [BinarySingleNaN.Bsign]; try discriminate Hn; apply C.
  Qed.

  Lemma L_mm : forall s s' A B, 0 <= A -> 0 <= B ->
    (s && negb s') || (negb s && negb s' && (A <? B)) || (s && s' && (B <? A)) =
    match magCmp s A s' B with Lt => true | Datatypes.Eq => s && negb s' | Gt => false end.
  Proof.
    intros s s' A B HA HB; unfold magCmp.
    destruct (Z.eqb_spec A 0); destruct (Z.eqb_spec B 0); cbn [andb]; destruct s, s'; cbn [andb orb negb]; try reflexivity;
      destruct (A ?= B) eqn:C1; destruct (B ?= A) eqn:C2; cmp_hyps;
      repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end; try reflexivity; lia.
  Qed.

  (* `-0 < +0`: the order used by FMIN / FMAX on non-NaN operands. *)
  Definition mmLt (x y : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) : bool :=
    match BinarySingleNaN.Bcompare x y with
    | Some Lt => true
    | Some Datatypes.Eq => BinarySingleNaN.Bsign x && negb (BinarySingleNaN.Bsign y)
    | _ => false
    end.

  (* Both NaN (or one NaN for FMINM / FMAXM): the canonical NaN; one NaN: the other operand. *)
  Definition mmSpec (isMax nanP : bool) (a b : bits W) : bits W :=
    let A := toB a in let B := toB b in
    ofB (if (BinarySingleNaN.is_nan A && BinarySingleNaN.is_nan B) ||
            (nanP && (BinarySingleNaN.is_nan A || BinarySingleNaN.is_nan B)) then BinarySingleNaN.B754_nan
         else if BinarySingleNaN.is_nan A then B
         else if BinarySingleNaN.is_nan B then A
         else if xorb (mmLt A B) isMax then A else B).

  Theorem fminmax_flocq : forall isMax nanP rm a b,
    (miscRef (mkOp true false false false isMax nanP Zmod.zero false) rm a b) @% "res" = mmSpec isMax nanP a b /\
    (miscRef (mkOp true false false false isMax nanP Zmod.zero false) rm a b) @% "flags" =
      mkFl (isSNaN e f Hf Hpe a || isSNaN e f Hf Hpe b) false false false false.
  Proof.
    intros isMax nanP rm a b. destruct (mm_core isMax nanP rm a b) as [-> ->]. rewrite (flip0 e f Hf Hpe b).
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    pose proof (HeM e f Hf Hpe) as He.
    unfold mmV, mmSpec; cbn [Fst Snd].
    rewrite (u_sign e f He Hf a sa Ea Ma HMa HEa Ha), (u_sign e f He Hf b sb Eb Mb HMb HEb Hb),
      (u_nan e f He Hf a sa Ea Ma HMa HEa Ha), (u_nan e f He Hf b sb Eb Mb HMb HEb Hb),
      (u_snan e f He Hf a sa Ea Ma HMa HEa Ha), (u_snan e f He Hf b sb Eb Mb HMb HEb Hb),
      (Hmag e f He Hf a sa Ea Ma HMa HEa Ha), (Hmag e f He Hf b sb Eb Mb HMb HEb Hb), xor_eval, mkFlags_eval.
    rewrite (isSNaN_eq e f Hf Hpe a sa Ea Ma HMa HEa Ha), (isSNaN_eq e f Hf Hpe b sb Eb Mb HMb HEb Hb),
      <- (nan_fields a sa Ea Ma HMa HEa Ha), <- (nan_fields b sb Eb Mb HMb HEb Hb).
    split; [| reflexivity].
    destruct (BinarySingleNaN.is_nan (toB a)) eqn:NA; destruct (BinarySingleNaN.is_nan (toB b)) eqn:NB; cbn [andb orb].
    - symmetry; apply (ofB_nan e f Hf Hpe).
    - destruct nanP; [symmetry; apply (ofB_nan e f Hf Hpe) | symmetry; apply (ofB_toB e f Hf Hpe b NB)].
    - rewrite andb_true_r. destruct nanP; [symmetry; apply (ofB_nan e f Hf Hpe) | symmetry; apply (ofB_toB e f Hf Hpe a NA)].
    - rewrite andb_false_r.
      unfold mmLt. rewrite (bcmp_fields a b sa Ea Ma sb Eb Mb HMa HEa Ha HMb HEb Hb NA NB),
        (sign_fields a sa Ea Ma HMa HEa Ha NA), (sign_fields b sb Eb Mb HMb HEb Hb NB).
      rewrite L_mm by (pose proof (mag_bound Ea Ma HMa HEa); pose proof (mag_bound Eb Mb HMb HEb); lia).
      destruct (magCmp _ _ _ _); cbv iota beta;
        match goal with |- (if ?c then _ else _) = _ => destruct c end;
        symmetry; first [apply (ofB_toB e f Hf Hpe a NA) | apply (ofB_toB e f Hf Hpe b NB)].
  Qed.
  (* ---------------------------------------------------------------------------
   * 3. FSGNJ / FSGNJN / FSGNJX (mode 0 / 1 / 2; mode 3 behaves as FSGNJX)
   * --------------------------------------------------------------------------- *)

  (* The sign bit of a pattern. *)
  Definition signBit (x : bits W) : bool := 2 ^ (f + e) <=? Zmod.to_Z x.

  Definition sjSign (md : bits 2) (sa sb : bool) : bool :=
    if Zmod.to_Z md =? 0 then sb else if Zmod.to_Z md =? 1 then negb sb else xorb sa sb.

  (* Bit level: the magnitude of `a` with the new sign. *)
  Definition sjSpec (md : bits 2) (a b : bits W) : bits W :=
    Zmod.of_Z _ (b2z (sjSign md (signBit a) (signBit b)) * 2 ^ (f + e) + Zmod.to_Z a mod 2 ^ (f + e)).

  Lemma signBit_fields : forall x s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M -> signBit x = s.
  Proof.
    intros x s E M HM HE Hx. unfold signBit; rewrite Hx. pose proof (mag_bound E M HM HE).
    destruct (Z.leb_spec (2 ^ (f + e)) (b2z s * 2 ^ (f + e) + E * 2 ^ f + M)); destruct s; cbn [b2z] in *; first [reflexivity | lia].
  Qed.

  Lemma sbit_eval : forall x : bits W,
    evalExpr (isNotZero (TruncMsb 1 (f + e) (Var type (Bit W) x))) = signBit x.
  Proof.
    intros x. pose proof (HeM e f Hf Hpe). rewrite evalExpr_isNotZero_bits; cbn [evalExpr].
    rewrite lastn_eval by lia. replace (f + e + 1 - 1) with (f + e) by lia. unfold signBit.
    pose proof (bits.unsigned_range x ltac:(lia)).
    assert (HW : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    destruct (Z.leb_spec (2 ^ (f + e)) (Zmod.to_Z x)).
    - rewrite <- (Z.div_unique (Zmod.to_Z x) (2 ^ (f + e)) 1 (Zmod.to_Z x - 2 ^ (f + e))) by lia. reflexivity.
    - rewrite Z.div_small by lia. reflexivity.
  Qed.

  Theorem fsgnj_bits : forall md rm a b,
    (miscRef (mkOp false true false false false false md false) rm a b) @% "res" = sjSpec md a b /\
    (miscRef (mkOp false true false false false false md false) rm a b) @% "flags" = mkFl false false false false false.
  Proof.
    intros md rm a b. destruct (sj_core md rm a b) as [-> ->]. rewrite (flip0 e f Hf Hpe b).
    unfold sjV; cbn [Fst Snd]. rewrite !sbit_eval, xor_eval, !eqb_md, noFlags_eval by lia. split; [| reflexivity].
    pose proof (HeM e f Hf Hpe). unfold sjSpec, sjSign.
    apply Zmod.unsigned_inj. cbn [evalExpr packSigned boolBit magOf cst]. rewrite unsigned_app_arith by lia.
    rewrite bits.unsigned_firstn, Zmod.unsigned_of_Z.
    assert (HW : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    pose proof (Z.mod_pos_bound (Zmod.to_Z a) (2 ^ (f + e)) ltac:(lia)).
    destruct (Zmod.to_Z md =? 0), (Zmod.to_Z md =? 1), (signBit a), (signBit b); cbn [negb xorb b2z];
      change (Zmod.unsigned (Zmod.of_Z (2 ^ 1) 1)) with 1; change (Zmod.unsigned (Zmod.of_Z (2 ^ 1) 0)) with 0;
      rewrite (Z.mod_small _ (2 ^ W)) by lia; lia.
  Qed.

  Lemma B2SF_Bopp_fields : forall (x : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) s E M,
    BinarySingleNaN.B2SF x = sfFields e f s E M -> BinarySingleNaN.B2SF (BinarySingleNaN.Bopp x) = sfFields e f (negb s) E M.
  Proof.
    intros [s0 | s0 | | s0 m ex Hb] s E M H; cbn [BinarySingleNaN.Bopp BinarySingleNaN.B2SF] in *; unfold sfFields in *;
      destruct (E =? 0), (M =? 0), (E =? 2 ^ e - 1); try discriminate H; try reflexivity; injection H; intros; subst; reflexivity.
  Qed.

  (* Flocq level: for a non-NaN `b`, the result is `a` or `Bopp a` (the sign from `Bsign`). *)
  Theorem fsgnj_flocq : forall md rm a b, BinarySingleNaN.is_nan (toB b) = false ->
    toB ((miscRef (mkOp false true false false false false md false) rm a b) @% "res") =
      (let A := toB a in
       if Bool.eqb (sjSign md (BinarySingleNaN.Bsign A) (BinarySingleNaN.Bsign (toB b))) (BinarySingleNaN.Bsign A)
       then A else BinarySingleNaN.Bopp A).
  Proof.
    intros md rm a b NB. rewrite (proj1 (fsgnj_bits md rm a b)). cbv zeta.
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    pose proof (HeM e f Hf Hpe) as He. pose proof (mag_bound Ea Ma HMa HEa) as HB.
    rewrite (sign_fields b sb Eb Mb HMb HEb Hb NB).
    set (s' := sjSign md sa sb).
    assert (HR : Zmod.to_Z (sjSpec md a b) = b2z s' * 2 ^ (f + e) + Ea * 2 ^ f + Ma).
    { unfold sjSpec. rewrite (signBit_fields a sa Ea Ma HMa HEa Ha), (signBit_fields b sb Eb Mb HMb HEb Hb). fold s'.
      rewrite Ha. replace (b2z sa * 2 ^ (f + e) + Ea * 2 ^ f + Ma) with (Ea * 2 ^ f + Ma + b2z sa * 2 ^ (f + e)) by ring.
      rewrite Z.mod_add, (Z.mod_small (Ea * 2 ^ f + Ma)) by lia. rewrite Zmod.unsigned_of_Z, Z.mod_small; [ring |].
      assert (HW : 2 ^ (f + e + 1) = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia). destruct s'; cbn [b2z]; lia. }
    pose proof (B2SF_toB_fields e f Hf Hpe a sa Ea Ma HMa HEa Ha) as FA.
    pose proof (B2SF_toB_fields e f Hf Hpe _ s' Ea Ma HMa HEa HR) as FR.
    destruct (BinarySingleNaN.is_nan (toB a)) eqn:NA.
    - destruct (toB a) eqn:TA; try discriminate NA.
      apply BinarySingleNaN.B2SF_inj. rewrite FR. cbn [BinarySingleNaN.B2SF] in FA.
      destruct (Bool.eqb _ _); cbn; unfold sfFields in *; destruct (Ea =? 0), (Ma =? 0), (Ea =? 2 ^ e - 1); congruence.
    - rewrite (sign_fields a sa Ea Ma HMa HEa Ha NA). fold s'.
      apply BinarySingleNaN.B2SF_inj. rewrite FR.
      destruct (Bool.eqb_spec s' sa) as [-> | Hn]; [exact (eq_sym FA) |].
      rewrite (B2SF_Bopp_fields _ sa Ea Ma FA). destruct s', sa; try (exfalso; apply Hn; reflexivity); reflexivity.
  Qed.
  (* ---------------------------------------------------------------------------
   * 4. FCLASS
   * --------------------------------------------------------------------------- *)

  (* The RISC-V class mask from Flocq's view of `a` (subnormal: significand below `2^f`). *)
  Definition fclassMask (a : bits W) : Z :=
    match toB a with
    | BinarySingleNaN.B754_infinity true => 1
    | BinarySingleNaN.B754_finite true m _ _ => if Zpos m <? 2 ^ f then 4 else 2
    | BinarySingleNaN.B754_zero true => 8
    | BinarySingleNaN.B754_zero false => 16
    | BinarySingleNaN.B754_finite false m _ _ => if Zpos m <? 2 ^ f then 32 else 64
    | BinarySingleNaN.B754_infinity false => 128
    | BinarySingleNaN.B754_nan => if isSNaN e f Hf Hpe a then 256 else 512
    end.

  Lemma or0r : forall n (x : bits n), Zmod.or x (Zmod.of_Z _ 0) = x.
  Proof. intros n x; apply Zmod.unsigned_inj; rewrite bits.unsigned_or, Zmod.unsigned_of_Z, Zmod_0_l, Z.lor_0_r; reflexivity. Qed.

  Lemma or0l : forall n (x : bits n), Zmod.or Zmod.zero x = x.
  Proof. intros n x; apply Zmod.unsigned_inj; rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l; reflexivity. Qed.

  Theorem fclass_flocq : forall rm a b,
    (miscRef (mkOp false false false true false false Zmod.zero false) rm a b) @% "xres" = Zmod.of_Z _ (fclassMask a) /\
    (miscRef (mkOp false false false true false false Zmod.zero false) rm a b) @% "flags" = mkFl false false false false false.
  Proof.
    intros rm a b. destruct (cls_core rm a b) as [-> ->].
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    pose proof (HeM e f Hf Hpe) as He.
    unfold clsV; cbn [Fst Snd].
    rewrite (u_sign e f He Hf a sa Ea Ma HMa HEa Ha), (u_zero e f He Hf a sa Ea Ma HMa HEa Ha),
      (u_inf e f He Hf a sa Ea Ma HMa HEa Ha), (u_nan e f He Hf a sa Ea Ma HMa HEa Ha),
      (u_snan e f He Hf a sa Ea Ma HMa HEa Ha), isZero_eval, (Hef e f He Hf a sa Ea Ma HMa HEa Ha), noFlags_eval.
    split; [| reflexivity].
    unfold fclassMask. rewrite (isSNaN_eq e f Hf Hpe a sa Ea Ma HMa HEa Ha).
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    pose proof (cls e f Hf Hpe a sa Ea Ma HMa HEa Ha) as C.
    destruct (toB a) as [s' | s' | | s' m ex Hb]; cbn [clsP] in C;
      repeat match goal with H : _ /\ _ |- _ => destruct H end; try subst s';
      try match goal with H : Zpos _ = _ |- _ => rewrite H end;
      repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end;
      repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end;
      try (exfalso; lia);
      try destruct sa; try destruct (Z.testbit Ma (f - 1)); cbn [andb orb negb];
      cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault cst];
      rewrite ?or0r, ?or0l; reflexivity.
  Qed.
  (* ---------------------------------------------------------------------------
   * 5. Zfa FLI: the constant table (`fliConstE`, used by the parent, not by `fpuCompute`)
   * --------------------------------------------------------------------------- *)

  Lemma fin_norm : forall x s E M, 0 <= M < 2 ^ f -> 1 <= E <= 2 ^ e - 2 ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    BinarySingleNaN.is_finite (toB x) = true /\
    BinarySingleNaN.B2R (toB x) = cond_Ropp s (F2R (Float radix2 (M + 2 ^ f) (E + eminF - 1))).
  Proof.
    intros x s E M HM HE Hx.
    rewrite <- BinarySingleNaN.is_finite_SF_B2SF, <- BinarySingleNaN.SF2R_B2SF, (B2SF_toB_fields e f Hf Hpe x s E M HM ltac:(lia) Hx).
    unfold sfFields. destruct (Z.eqb_spec E 0); [lia |]. destruct (Z.eqb_spec E (2 ^ e - 1)); [lia |].
    cbn [BinarySingleNaN.is_finite_SF BinarySingleNaN.SF2R]. split; [reflexivity |].
    rewrite Z2Pos.id by (pose proof (Z.pow_pos_nonneg 2 f); lia). apply F2R_cond_Zopp.
  Qed.

  Lemma fin_sub : forall x s M, 0 < M < 2 ^ f ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + 0 * 2 ^ f + M ->
    BinarySingleNaN.is_finite (toB x) = true /\
    BinarySingleNaN.B2R (toB x) = cond_Ropp s (F2R (Float radix2 M eminF)).
  Proof.
    intros x s M HM Hx. pose proof (HeM e f Hf Hpe). pose proof (Z.pow_pos_nonneg 2 e).
    rewrite <- BinarySingleNaN.is_finite_SF_B2SF, <- BinarySingleNaN.SF2R_B2SF, (B2SF_toB_fields e f Hf Hpe x s 0 M ltac:(lia) ltac:(lia) Hx).
    unfold sfFields. rewrite Z.eqb_refl. destruct (Z.eqb_spec M 0); [lia |].
    cbn [BinarySingleNaN.is_finite_SF BinarySingleNaN.SF2R]. split; [reflexivity |].
    rewrite Z2Pos.id by lia. apply F2R_cond_Zopp.
  Qed.

  (* The value `(-1)^sg * m * 2^k` of a table entry `(sg, m, k)`: `+-inf` above the range, otherwise
   * exact (normal or subnormal) when `k` is not below the subnormal range. *)
  Definition fliEntryOK (t : Z * Z * Z) (B : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) : Prop :=
    let '(sg, m, k) := t in
    if fpEmax e <? k + Z.log2 m then B = BinarySingleNaN.B754_infinity (sg =? 1)
    else fpEmin e - f <= k ->
      BinarySingleNaN.is_finite B = true /\
      BinarySingleNaN.B2R B = cond_Ropp (sg =? 1) (IZR m * bpow radix2 k).

  Lemma enc_toZ : forall sg v, (sg = 0 \/ sg = 1) -> 0 <= v < 2 ^ (f + e) ->
    Zmod.to_Z (Zmod.of_Z (2 ^ W) (sg * 2 ^ (f + e) + v)) = b2z (sg =? 1) * 2 ^ (f + e) + v.
  Proof.
    intros sg v Hsg Hv. pose proof (HeM e f Hf Hpe).
    assert (HW : 2 ^ W = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    rewrite Zmod.unsigned_of_Z, Z.mod_small; destruct Hsg; subst; cbn [Z.eqb b2z Pos.eqb]; lia.
  Qed.

  Lemma fli_enc : forall sg m k, (sg = 0 \/ sg = 1) -> 1 <= m -> Z.log2 m <= f ->
    fliEntryOK (sg, m, k) (toB (Zmod.of_Z _ (fliEncode e f (sg, m, k)))).
  Proof.
    intros sg m k Hsg Hm Hpf. unfold fliEncode, fliEntryOK; cbv zeta.
    pose proof (Z.log2_spec m ltac:(lia)) as [Hp1 Hp2]. pose proof (Z.log2_nonneg m).
    set (p := Z.log2 m) in *. rewrite Z.pow_succ_r in Hp2 by lia.
    pose proof (HeM e f Hf Hpe) as He.
    assert (HP : 2 ^ e = 2 * 2 ^ (e - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; lia).
    assert (H2f : 2 ^ f = 2 ^ p * 2 ^ (f - p)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    pose proof (Z.pow_pos_nonneg 2 (f - p) ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (e - 1) ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_pos_nonneg 2 p ltac:(lia) ltac:(lia)).
    unfold fpEmax, fpEmin, fpBias, infMagZ.
    destruct (Z.ltb_spec (2 ^ (e - 1) - 1) (k + p)) as [Hov | Hov].
    - apply BinarySingleNaN.B2SF_inj.
      assert (Hv : 0 <= (2 ^ e - 1) * 2 ^ f < 2 ^ (f + e)) by (pose proof (Z.pow_pos_nonneg 2 f ltac:(lia) ltac:(lia));
        split; [apply Z.mul_nonneg_nonneg; lia | rewrite Hfe; lia]).
      rewrite (B2SF_toB_fields e f Hf Hpe _ (sg =? 1) (2 ^ e - 1) 0 ltac:(lia) ltac:(lia)) by (rewrite enc_toZ by assumption; ring).
      unfold sfFields. destruct (Z.eqb_spec (2 ^ e - 1) 0); [lia |]. rewrite Z.eqb_refl. reflexivity.
    - destruct (Z.leb_spec (1 - (2 ^ (e - 1) - 1)) (k + p)) as [Hn | Hn].
      + intros _.
        set (E := k + p + (2 ^ (e - 1) - 1)). set (M := (m - 2 ^ p) * 2 ^ (f - p)).
        assert (HM : 0 <= M < 2 ^ f).
        { unfold M; split; [apply Z.mul_nonneg_nonneg; lia |].
          assert ((m - 2 ^ p) * 2 ^ (f - p) <= (2 ^ p - 1) * 2 ^ (f - p)) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
        assert (HE : 1 <= E <= 2 ^ e - 2) by (unfold E; lia).
        assert (Hv : 0 <= E * 2 ^ f + M < 2 ^ (f + e)).
        { assert (E * 2 ^ f <= (2 ^ e - 2) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia).
          assert (0 <= E * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia). rewrite Hfe; lia. }
        match goal with |- context [toB ?y] =>
          destruct (fin_norm y (sg =? 1) E M HM HE ltac:(rewrite enc_toZ by assumption; ring)) as [F1 F2] end.
        split; [exact F1 |]. rewrite F2. f_equal.
        replace (M + 2 ^ f) with (m * 2 ^ (f - p)) by (unfold M; rewrite H2f; ring).
        replace (E + eminF - 1) with (k - (f - p)) by (unfold E, SpecFloat.emin; lia).
        rewrite F2R_scale by lia. reflexivity.
      + intros Hk.
        set (d := k - (1 - (2 ^ (e - 1) - 1)) + f).
        assert (HM : 0 < m * 2 ^ d < 2 ^ f).
        { pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) ltac:(unfold d; lia)). split; [apply Z.mul_pos_pos; lia |].
          assert (m * 2 ^ d < 2 * 2 ^ p * 2 ^ d) by (apply Z.mul_lt_mono_pos_r; lia).
          assert (2 * 2 ^ p * 2 ^ d = 2 ^ (p + 1 + d)) by (rewrite !Z.pow_add_r by (unfold d; lia); ring).
          assert (2 ^ (p + 1 + d) <= 2 ^ f) by (apply Z.pow_le_mono_r; unfold d; lia). lia. }
        match goal with |- context [toB ?y] =>
          destruct (fin_sub y (sg =? 1) (m * 2 ^ d) HM ltac:(rewrite enc_toZ by (try assumption; assert (2 ^ f <= 2 ^ (f + e)) by (apply Z.pow_le_mono_r; lia); lia); ring)) as [F1 F2] end.
        split; [exact F1 |]. rewrite F2. f_equal.
        replace eminF with (k - d) by (unfold d, SpecFloat.emin; lia).
        rewrite F2R_scale by (unfold d; lia). reflexivity.
  Qed.
  (* The RISC-V Zfa FLI constants `(sg, m, k)` = `(-1)^sg * m * 2^k` for indices 2 .. 29. *)
  Definition fliRV : list (Z * Z * Z) :=
    [ (0, 1, -16) ; (0, 1, -15) ; (0, 1, -8) ; (0, 1, -7) ; (0, 1, -4) ; (0, 1, -3) ;
      (0, 1, -2) ; (0, 5, -4) ; (0, 3, -3) ; (0, 7, -4) ; (0, 1, -1) ; (0, 5, -3) ;
      (0, 3, -2) ; (0, 7, -3) ; (0, 1, 0) ; (0, 5, -2) ; (0, 3, -1) ; (0, 7, -2) ;
      (0, 1, 1) ; (0, 5, -1) ; (0, 3, 0) ; (0, 1, 2) ; (0, 1, 3) ; (0, 1, 4) ;
      (0, 1, 7) ; (0, 1, 8) ; (0, 1, 15) ; (0, 1, 16) ].

  (* The table entry selected by index `i`. *)
  Definition fliVal (i : Z) : bits W := evalExpr (fliConstE e f type (Const type (Bit 5) (Zmod.of_Z _ i))).

  (* Index 0: -1.0; 1: the minimum positive normal; 2 .. 29: `fliRV`; 30: +inf; 31: the canonical NaN. *)
  Definition fliOK (n : nat) (B : BinarySingleNaN.binary_float (f + 1) (2 ^ (e - 1))) : Prop :=
    match n with
    | 1%nat => BinarySingleNaN.is_finite B = true /\ BinarySingleNaN.B2R B = bpow radix2 (fpEmin e)
    | 30%nat => B = BinarySingleNaN.B754_infinity false
    | 31%nat => B = BinarySingleNaN.B754_nan
    | _ => fliEntryOK (nth n ((1, 1, 0) :: (0, 0, 0) :: fliRV) (0, 0, 0)) B
    end.

  Lemma fliSel_eval : forall vs k0 i, 0 <= k0 <= i -> i < k0 + Z.of_nat (length vs) -> k0 + Z.of_nat (length vs) <= 32 ->
    evalExpr (fliSel e f type (Const type (Bit 5) (Zmod.of_Z _ i)) k0 vs) = Zmod.of_Z _ (nth (Z.to_nat (i - k0)) vs 0).
  Proof.
    induction vs as [| v vs IH]; intros k0 i H1 H2 H3; cbn [length] in *; [lia |].
    cbn [fliSel evalExpr cst isEq KindCustomInd]. rewrite zeqb, !Zmod.unsigned_of_Z, !Z.mod_small by (cbn; lia).
    destruct (Z.eqb_spec i k0) as [-> | Hn]; [rewrite Z.sub_diag; reflexivity |].
    rewrite IH by lia. replace (Z.to_nat (i - k0)) with (S (Z.to_nat (i - (k0 + 1)))) by lia; reflexivity.
  Qed.

  Lemma fliVal_nth : forall n, (n < 32)%nat -> fliVal (Z.of_nat n) = Zmod.of_Z _ (nth n (fliTable e f) 0).
  Proof.
    intros n Hn. unfold fliVal, fliConstE.
    assert (Hl : length (fliTable e f) = 32%nat) by reflexivity.
    rewrite fliSel_eval by lia. rewrite Z.sub_0_r, Nat2Z.id; reflexivity.
  Qed.

  Lemma fli_minnorm : BinarySingleNaN.is_finite (toB (Zmod.of_Z _ (2 ^ f))) = true /\
    BinarySingleNaN.B2R (toB (Zmod.of_Z _ (2 ^ f))) = bpow radix2 (fpEmin e).
  Proof.
    pose proof (HeM e f Hf Hpe). assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (2 ^ f < 2 ^ W) by (apply Z.pow_lt_mono_r; lia).
    destruct (fin_norm (Zmod.of_Z _ (2 ^ f)) false 1 0 ltac:(lia) ltac:(lia)) as [F1 F2].
    { rewrite Zmod.unsigned_of_Z, Z.mod_small by lia. cbn [b2z]. ring. }
    split; [exact F1 |]. rewrite F2. cbn [cond_Ropp].
    replace (0 + 2 ^ f) with (1 * 2 ^ f) by ring.
    replace (1 + eminF - 1) with (fpEmin e - f) by (unfold fpEmin, fpBias, SpecFloat.emin; lia).
    rewrite F2R_scale by lia. unfold F2R; cbn [Fnum Fexp]. apply Rmult_1_l.
  Qed.

  Lemma fli_inf : toB (Zmod.of_Z _ (infMagZ e f)) = BinarySingleNaN.B754_infinity false.
  Proof.
    pose proof (HeM e f Hf Hpe). assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    apply BinarySingleNaN.B2SF_inj.
    rewrite (B2SF_toB_fields e f Hf Hpe _ false (2 ^ e - 1) 0 ltac:(lia) ltac:(lia)).
    - unfold sfFields. destruct (Z.eqb_spec (2 ^ e - 1) 0); [lia |]. rewrite Z.eqb_refl. reflexivity.
    - pose proof (mag_bound (2 ^ e - 1) 0 ltac:(lia) ltac:(lia)).
      assert (2 ^ (f + e) < 2 ^ W) by (apply Z.pow_lt_mono_r; lia).
      rewrite Zmod.unsigned_of_Z, Z.mod_small by (unfold infMagZ; lia). unfold infMagZ; cbn [b2z]. ring.
  Qed.

  Lemma fli_nan : toB (Zmod.of_Z _ (qnanMagZ e f)) = BinarySingleNaN.B754_nan.
  Proof.
    pose proof (HeM e f Hf Hpe). assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    assert (Hf1 : 2 ^ f = 2 * 2 ^ (f - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    pose proof (Z.pow_pos_nonneg 2 (f - 1) ltac:(lia) ltac:(lia)).
    pose proof (mag_bound (2 ^ e - 1) (2 ^ (f - 1)) ltac:(lia) ltac:(lia)).
    assert (Hx : Zmod.to_Z (Zmod.of_Z (2 ^ W) (qnanMagZ e f)) = b2z false * 2 ^ (f + e) + (2 ^ e - 1) * 2 ^ f + 2 ^ (f - 1)).
    { assert (2 ^ (f + e) < 2 ^ W) by (apply Z.pow_lt_mono_r; lia).
      rewrite Zmod.unsigned_of_Z, Z.mod_small by (unfold qnanMagZ, infMagZ; lia). unfold qnanMagZ, infMagZ; cbn [b2z]. ring. }
    pose proof (nan_fields _ false (2 ^ e - 1) (2 ^ (f - 1)) ltac:(lia) ltac:(lia) Hx) as HN.
    rewrite Z.eqb_refl in HN. destruct (Z.eqb_spec (2 ^ (f - 1)) 0); [lia |].
    destruct (toB (Zmod.of_Z _ (qnanMagZ e f))); cbn in HN; congruence.
  Qed.

  (* Entry 31 is the RISC-V canonical NaN (the encoding of Flocq's NaN). *)
  Lemma fli_canon : fliVal 31 = ofB BinarySingleNaN.B754_nan.
  Proof. rewrite (ofB_nan e f Hf Hpe). change 31 with (Z.of_nat 31). rewrite fliVal_nth by lia. reflexivity. Qed.

  Ltac fli_gen :=
    apply fli_enc; [lia | lia |];
    match goal with |- Z.log2 ?m <= _ => let v := eval vm_compute in (Z.log2 m) in change (Z.log2 m) with v end; lia.

  Theorem fli_flocq : forall n, (n < 32)%nat -> fliOK n (toB (fliVal (Z.of_nat n))).
  Proof.
    intros n Hn. rewrite fliVal_nth by exact Hn.
    do 32 (destruct n as [| n]; [cbn [fliOK nth fliTable map app];
      first [exact fli_minnorm | exact fli_inf | exact fli_nan | fli_gen] |]).
    lia.
  Qed.
End Misc.
