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
 * FADD / FSUB against Flocq's `Bplus` / `Bminus` (`Add.v`).
 *
 * `faddRef rm a b` / `fsubRef rm a b` are the reference core (`FpCoreRef.fpuComputeRef`) on a
 * decoded FADD / FSUB.  `fadd_flocq` / `fsub_flocq`: the result is Flocq's `Bplus` / `Bminus`
 * (in `BinarySingleNaN`, NaN encoded as the RISC-V canonical NaN) and the flags are the IEEE
 * flags of rounding the exact sum / difference (`Flags.v`), with NV for a signaling NaN operand
 * or `inf - inf`.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Reals Lia Lra Bool.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Core Calc.Bracket IEEE754.BinarySingleNaN.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Fpu Require Import FpUtil FpCore FpCoreRef FpUtilLemmas ExpShift IntMulProof.
From Fpu.FlocqProof Require Import Glue Flags Decode RoundBits RoundLoc RoundCore NormRound Unpack Mul.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

(* ---------------------------------------------------------------------------
 * Integer model of the aligned sum and the exact real sum
 * --------------------------------------------------------------------------- *)

Section Arith.
  Variable f : Z.
  Hypothesis Hf : 2 <= f.

  Definition nAdd (eS : bool) (SB SS D : Z) : Z :=
    if eS then 8 * SB * 2 ^ D - 8 * SS else 8 * SB * 2 ^ D + 8 * SS.
  Definition stAdd (SS D : Z) : bool := negb ((8 * SS) mod 2 ^ D =? 0).
  Definition rAdd (eS : bool) (SB SS D : Z) : Z :=
    if eS then 8 * SB - 8 * SS / 2 ^ D - b2z (stAdd SS D) else 8 * SB + 8 * SS / 2 ^ D.

  Lemma sh_eq : forall SS D, 0 <= 8 * SS < 2 ^ (f + 4) -> 0 <= D ->
    8 * SS / 2 ^ Z.min D (f + 5) = 8 * SS / 2 ^ D /\ (8 * SS) mod 2 ^ Z.min D (f + 5) = (8 * SS) mod 2 ^ D.
  Proof.
    intros SS D HS HD. destruct (Z.le_ge_cases D (f + 5)) as [H | H]; [rewrite Z.min_l by lia; split; reflexivity |].
    rewrite Z.min_r by lia.
    assert (2 ^ (f + 4) <= 2 ^ (f + 5)) by (apply Z.pow_le_mono_r; lia).
    assert (2 ^ (f + 5) <= 2 ^ D) by (apply Z.pow_le_mono_r; lia).
    rewrite !Z.div_small, !Z.mod_small by lia; split; reflexivity.
  Qed.

  Lemma add_int : forall eS SB SS D,
    2 ^ f <= SB < 2 ^ (f + 1) -> 2 ^ f <= SS < 2 ^ (f + 1) -> 0 <= D -> (D = 0 -> SS <= SB) ->
    rAdd eS SB SS D = nAdd eS SB SS D / 2 ^ D /\
    stAdd SS D = negb (nAdd eS SB SS D mod 2 ^ D =? 0) /\
    0 <= nAdd eS SB SS D /\ 0 <= rAdd eS SB SS D < 2 ^ (f + 5) /\
    (stAdd SS D = true -> 2 ^ (f + 2) <= rAdd eS SB SS D).
  Proof.
    intros eS SB SS D HB HS HD H0.
    assert (P1 : 2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (P2 : 2 ^ (f + 2) = 4 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (P5 : 2 ^ (f + 5) = 32 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (HP : 0 < 2 ^ D) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_mod (8 * SS) (2 ^ D) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (8 * SS) (2 ^ D) HP) as Hm.
    assert (Hq0 : 0 <= 8 * SS / 2 ^ D) by (apply Z.div_pos; lia).
    unfold rAdd, nAdd, stAdd.
    set (q := 8 * SS / 2 ^ D) in *. set (m := (8 * SS) mod 2 ^ D) in *.
    (* the small operand's contribution *)
    assert (Hq : (D = 0 /\ q = 8 * SS /\ m = 0) \/ (1 <= D <= 3 /\ q <= 4 * SS /\ m = 0) \/ (4 <= D /\ q < 2 ^ f)).
    { destruct (Z.eq_dec D 0) as [-> | HD1].
      - left. unfold q, m; rewrite Z.pow_0_r, Z.div_1_r, Z.mod_1_r; lia.
      - right. assert (H2 : 2 <= 2 ^ D) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
        assert (Hq4 : q <= 8 * SS / 2) by (apply Z.div_le_compat_l; lia).
        assert (8 * SS / 2 = 4 * SS) by (symmetry; apply Z.div_unique with 0; lia).
        destruct (Z_le_gt_dec D 3) as [HD3 | HD3].
        + left. split; [lia | split; [lia |]].
          unfold m. replace 8 with (2 ^ (3 - D) * 2 ^ D) by (rewrite <- Z.pow_add_r by lia; replace (3 - D + D) with 3 by lia; reflexivity).
          rewrite <- Z.mul_assoc, (Z.mul_comm (2 ^ D)), Z.mul_assoc. apply Z.mod_mul; lia.
        + right. split; [lia |].
          assert (H16 : 16 <= 2 ^ D) by (change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia).
          assert (q <= 8 * SS / 16) by (apply Z.div_le_compat_l; lia).
          assert (8 * SS / 16 < 2 ^ f) by (apply Z.div_lt_upper_bound; lia). lia. }
    clearbody q m.
    assert (HSB : 8 * SS <= 8 * SB * 2 ^ D).
    { destruct Hq as [(-> & _ & _) | [(? & _ & _) | (? & _)]]; [rewrite Z.pow_0_r; lia | |];
        assert (2 <= 2 ^ D) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia); nia. }
    destruct eS.
    - destruct (Z.eqb_spec m 0) as [Em | Em]; cbn [negb b2z].
      + rewrite Em in Hdm.
        assert (E1 : 8 * SB * 2 ^ D - 8 * SS = 2 ^ D * (8 * SB - q) + 0) by (rewrite Hdm; ring).
        rewrite E1, Z.add_0_r, (Z.mul_comm (2 ^ D)), Z.div_mul, Z.mod_mul by lia.
        split; [lia |]. split; [reflexivity |]. split; [lia |].
        split; [destruct Hq as [(? & ? & ?) | [(? & ? & ?) | (? & ?)]]; lia | discriminate].
      + assert (E1 : 8 * SB * 2 ^ D - 8 * SS = (8 * SB - q - 1) * 2 ^ D + (2 ^ D - m)) by (rewrite Hdm; ring).
        rewrite E1. rewrite <- (Z.div_unique _ _ (8 * SB - q - 1) (2 ^ D - m)) by lia.
        rewrite <- (Z.mod_unique _ _ (8 * SB - q - 1) (2 ^ D - m)) by lia.
        replace (2 ^ D - m =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        destruct Hq as [(_ & _ & ?) | [(_ & _ & ?) | (_ & ?)]]; [lia | lia |].
        split; [lia |]. split; [reflexivity |]. split; [lia |]. split; lia.
    - assert (E1 : 8 * SB * 2 ^ D + 8 * SS = (8 * SB + q) * 2 ^ D + m) by (rewrite Hdm; ring).
      rewrite E1. rewrite <- (Z.div_unique _ _ (8 * SB + q) m) by lia.
      rewrite <- (Z.mod_unique _ _ (8 * SB + q) m) by lia.
      split; [reflexivity |]. split; [reflexivity |]. split; [lia |].
      split; [destruct Hq as [(? & ? & ?) | [(? & ? & ?) | (? & ?)]]; lia | lia].
  Qed.

  Lemma sum_val : forall sB sS SB SS XB XS, XS <= XB ->
    (cond_Ropp sB (F2R (Float radix2 SB (XB - f))) + cond_Ropp sS (F2R (Float radix2 SS (XS - f))))%R =
    cond_Ropp sB (F2R (Float radix2 (nAdd (negb (Bool.eqb sB sS)) SB SS (XB - XS)) (XS - f - 3))).
  Proof.
    intros sB sS SB SS XB XS HX.
    assert (H1 : bpow radix2 (XB - f) = (IZR (2 ^ (XB - XS)) * 8 * bpow radix2 (XS - f - 3))%R).
    { rewrite <- bpow_2 by lia. change 8%R with (bpow radix2 3). rewrite <- !bpow_plus. f_equal; lia. }
    assert (H2 : bpow radix2 (XS - f) = (8 * bpow radix2 (XS - f - 3))%R).
    { change 8%R with (bpow radix2 3). rewrite <- !bpow_plus. f_equal; lia. }
    rewrite !F2R_eq, H1, H2. unfold nAdd.
    destruct sB, sS; cbn [cond_Ropp Bool.eqb negb];
      rewrite ?minus_IZR, ?plus_IZR, !mult_IZR; ring.
  Qed.
End Arith.

(* `alignAdd` as integer arithmetic. *)
Section Bits.
  Variable e : Z.
  Hypothesis He : 2 <= e.
  Local Abbreviation XK := (Bit (e + 3)).

  Definition alignV (Wd : Z) (sB sS : bool) (xB xS : bits (e + 3)) (big sm : bits Wd) : type (AlignK Wd) :=
    let d := evalExpr (Sub (Var type XK xB) (Var type XK xS)) in
    let sh := evalExpr (ITE (Ult (Var type XK d) (cst (e + 3) Wd)) (Var type XK d) (cst (e + 3) Wd)) in
    let smSh := evalExpr (Srl (Var type (Bit Wd) sm) (Var type XK sh)) in
    let st := evalExpr (isNotZero (And [Var type (Bit Wd) sm; Not (Sll (cst Wd (-1)) (Var type XK sh))])) in
    let effSub := evalExpr (Not (Eq (Var type Bool sB) (Var type Bool sS))) in
    let r := evalExpr (ITE (Var type Bool effSub)
                (Sub (Sub (Var type (Bit Wd) big) (Var type (Bit Wd) smSh)) (ITE (Var type Bool st) (cst Wd 1) (cst Wd 0)))
                (Add [Var type (Bit Wd) big; Var type (Bit Wd) smSh])) in
    (r ,, (st ,, (effSub ,, tt))).

  Lemma alignAdd_V : forall Wd sB sS xB xS big sm,
    evalLetExpr (alignAdd e type Wd sB sS xB xS big sm) = alignV Wd sB sS xB xS big sm.
  Proof. intros; exact eq_refl. Qed.

  Lemma pe3 : 2 ^ (e + 3) = 16 * 2 ^ (e - 1).
  Proof. replace (e + 3) with ((e - 1) + 4) by lia; rewrite Z.pow_add_r by lia; lia. Qed.

  Lemma alignAdd_vals : forall Wd sB sS (xB xS : bits (e + 3)) (big sm : bits Wd) BV SV,
    1 <= Wd < 2 ^ (e + 2) -> 0 <= Zmod.signed xB - Zmod.signed xS < 2 ^ (e + 2) ->
    Zmod.to_Z big = BV -> Zmod.to_Z sm = SV ->
    let sh := Z.min (Zmod.signed xB - Zmod.signed xS) Wd in
    let q := SV / 2 ^ sh in
    let st := negb (SV mod 2 ^ sh =? 0) in
    let r := if negb (Bool.eqb sB sS) then BV - q - b2z st else BV + q in
    0 <= r < 2 ^ Wd ->
    Zmod.to_Z (evalLetExpr (alignAdd e type Wd sB sS xB xS big sm)).(Fst) = r /\
    (evalLetExpr (alignAdd e type Wd sB sS xB xS big sm)).(Snd).(Fst) = st.
  Proof.
    intros Wd sB sS xB xS big sm BV SV HW HD Hbig Hsm sh q st r Hr.
    rewrite alignAdd_V; unfold alignV; cbv zeta; cbn [Fst Snd].
    assert (P2 : 2 ^ (e + 2) < 2 ^ (e + 3)) by (apply Z.pow_lt_mono_r; lia).
    set (d := evalExpr (Sub (Var type XK xB) (Var type XK xS))).
    assert (Hd : Zmod.to_Z d = Zmod.signed xB - Zmod.signed xS).
    { unfold d; rewrite (sub_eval (e + 3) ltac:(lia)); cbn [evalExpr].
      rewrite <- (Zmod.of_Z_signed xB), <- (Zmod.of_Z_signed xS) at 1.
      rewrite <- Zmod.of_Z_sub; apply tz_ofZ; lia. }
    clearbody d.
    set (sh' := evalExpr (ITE (Ult (Var type XK d) (cst (e + 3) Wd)) (Var type XK d) (cst (e + 3) Wd))).
    assert (Hsh : Zmod.to_Z sh' = sh).
    { unfold sh', sh; cbn [evalExpr cst]. rewrite (tz_ofZ (e + 3) Wd) by lia. rewrite Hd.
      destruct (Z.ltb_spec (Zmod.signed xB - Zmod.signed xS) Wd).
      - rewrite Z.min_l by lia; exact Hd.
      - rewrite Z.min_r by lia; apply tz_ofZ; lia. }
    clearbody sh'.
    assert (Hsh0 : 0 <= sh <= Wd) by (unfold sh; lia).
    set (smSh := evalExpr (Srl (Var type (Bit Wd) sm) (Var type XK sh'))).
    assert (HsmSh : Zmod.to_Z smSh = q).
    { unfold smSh, q; cbn [evalExpr]. rewrite tz_sru by lia. rewrite Hsm, Hsh; reflexivity. }
    clearbody smSh.
    set (st' := evalExpr (isNotZero (And [Var type (Bit Wd) sm; Not (Sll (cst Wd (-1)) (Var type XK sh'))]))).
    assert (Hst : st' = st).
    { unfold st', st. rewrite evalExpr_isNotZero_bits.
      cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd evalNot cst].
      rewrite unsigned_and_m1_l by lia. rewrite Hsh. rewrite tz_lowmask by lia. rewrite Hsm; reflexivity. }
    clearbody st'. split; [| exact Hst].
    assert (HE : evalExpr (Not (Eq (Var type Bool sB) (Var type Bool sS))) = negb (Bool.eqb sB sS)) by reflexivity.
    rewrite HE. cbn [evalExpr]. unfold r in *.
    pose proof (bits.unsigned_range big ltac:(lia)) as Rb.
    pose proof (bits.unsigned_range smSh ltac:(lia)) as Rs.
    destruct (negb (Bool.eqb sB sS)).
    - rewrite !(sub_eval Wd ltac:(lia)); cbn [evalExpr].
      rewrite !Zmod.unsigned_sub, Hbig, HsmSh.
      assert (2 <= 2 ^ Wd) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
      rewrite <- Hst in Hr |- *. destruct st'; cbn [evalExpr cst b2z] in *; rewrite (tz_ofZ Wd) by lia;
        rewrite Zminus_mod_idemp_l; apply Z.mod_small; lia.
    - cbn [fold_left map evalBinary KindCustomInd getDefault evalExpr].
      rewrite !Zmod.unsigned_add, Zmod.unsigned_0, Hbig, HsmSh, Z.add_0_l.
      rewrite (Z.mod_small BV) by lia. apply Z.mod_small; lia.
  Qed.
End Bits.

Section Add.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).
  Local Abbreviation isSN := (isSNaN e f Hf Hpe).

  Local Instance precGtA : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance precLtA : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  (* The decoded FADD (`negB = false`) / FSUB (`negB = true`). *)
  Definition opAdd (negB : bool) : type FpOpDK :=
    (true ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,, (false ,,
    (false ,, (false ,, (false ,, (negB ,, (false ,, (false ,, (false ,, (false ,,
    (Zmod.zero ,, (false ,, (false ,, (false ,, (false ,, tt)))))))))))))))))))))).

  Definition reqA (op : type FpOpDK) (rm : bits 3) (a b c : bits W) (x : bits xlen) : type (FpReqK e f xlen) :=
    (op ,, (rm ,, (a ,, (b ,, (c ,, (x ,, tt)))))).

  Definition faddRef (rm : bits 3) (a b : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqA (opAdd false) rm a b Zmod.zero Zmod.zero)).

  Definition fsubRef (rm : bits 3) (a b : bits W) : type (FpResK e f xlen) :=
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqA (opAdd true) rm a b Zmod.zero Zmod.zero)).

  (* IEEE flags of FADD. *)
  Definition addFlags (rm : bits 3) (a b : bits W) : bits 5 :=
    match toB a, toB b with
    | BinarySingleNaN.B754_nan, _ | _, BinarySingleNaN.B754_nan =>
        mkFl (isSN a || isSN b) false false false false
    | BinarySingleNaN.B754_infinity sa, BinarySingleNaN.B754_infinity sb =>
        mkFl (negb (Bool.eqb sa sb)) false false false false
    | BinarySingleNaN.B754_finite _ _ _ _, BinarySingleNaN.B754_finite _ _ _ _ =>
        finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
          (Rplus (BinarySingleNaN.B2R (toB a)) (BinarySingleNaN.B2R (toB b)))
    | _, _ => mkFl false false false false false
    end.

  (* IEEE flags of FSUB. *)
  Definition subFlags (rm : bits 3) (a b : bits W) : bits 5 :=
    match toB a, toB b with
    | BinarySingleNaN.B754_nan, _ | _, BinarySingleNaN.B754_nan =>
        mkFl (isSN a || isSN b) false false false false
    | BinarySingleNaN.B754_infinity sa, BinarySingleNaN.B754_infinity sb =>
        mkFl (Bool.eqb sa sb) false false false false
    | BinarySingleNaN.B754_finite _ _ _ _, BinarySingleNaN.B754_finite _ _ _ _ =>
        finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm)
          (Rminus (BinarySingleNaN.B2R (toB a)) (BinarySingleNaN.B2R (toB b)))
    | _, _ => mkFl false false false false false
    end.

  Definition fadd_flocq : Prop :=
    forall rm a b,
      (faddRef rm a b) @% "res" = ofB (BinarySingleNaN.Bplus (modeOf rm) (toB a) (toB b)) /\
      (faddRef rm a b) @% "flags" = addFlags rm a b.

  Definition fsub_flocq : Prop :=
    forall rm a b,
      (fsubRef rm a b) @% "res" = ofB (BinarySingleNaN.Bminus (modeOf rm) (toB a) (toB b)) /\
      (fsubRef rm a b) @% "flags" = subFlags rm a b.

  (* ---------------------------------------------------------------------------
   * The ADD path of the core
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

  Definition addCoreT (negB : bool) (rm : bits 3) (a b : bits W) : type (FpOutK e f) :=
    let b2 := evalExpr (flipSign e f type (And [ConstBool true; ConstBool negB]) b) in
    evalLetExpr (addCore false e f type rm a b2 (unp a) (unp b2)).

  (* The finite path (`normRound` on the aligned sum), transcribed. *)
  Definition addNrm (rm : bits 3) (sa sb : bool) (xa xb : bits (e + 3)) (siga sigb : bits (f + 1)) : type (FpOutK e f) :=
    let xGt := evalExpr (Slt (Var type XK xb) (Var type XK xa)) in
    let xEq := evalExpr (Eq (Var type XK xa) (Var type XK xb)) in
    let aBig := evalExpr (Or [Var type Bool xGt; And [Var type Bool xEq; Not (Ult (Var type (Bit (f + 1)) siga) (Var type (Bit (f + 1)) sigb))]]) in
    let sBig := (if aBig then sa else sb) in
    let sSm := (if aBig then sb else sa) in
    let xBig := (if aBig then xa else xb) in
    let xSm := (if aBig then xb else xa) in
    let big := evalExpr (Sll (zext (f + 1) (f + 5) (ITE (Var type Bool aBig) (Var type (Bit (f + 1)) siga) (Var type (Bit (f + 1)) sigb))) (cst (f + 5) 3)) in
    let sm := evalExpr (Sll (zext (f + 1) (f + 5) (ITE (Var type Bool aBig) (Var type (Bit (f + 1)) sigb) (Var type (Bit (f + 1)) siga))) (cst (f + 5) 3)) in
    let al := evalLetExpr (alignAdd e type (f + 5) sBig sSm xBig xSm big sm) in
    let r := al.(Fst) in
    let st := al.(Snd).(Fst) in
    let xR := evalExpr (Add [Var type XK xBig; cst (e + 3) 1]) in
    let sR := evalExpr (ITE (And [isZero (Var type (Bit (f + 5)) r); Not (Var type Bool st)])
                            (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) (Var type Bool sBig)) in
    evalLetExpr (normRound false e f type (f + 5) sR xR r st rm).

  (* `addCore false`, transcribed. *)
  Definition addV (rm : bits 3) (a b : bits W) (ua ub : type (FpUnpK e f)) : type (FpOutK e f) :=
    let sa := uSign ua in let sb := uSign ub in
    let eqS := evalExpr (Eq (Var type Bool sa) (Var type Bool sb)) in
    let isDN := evalExpr (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) in
    let zzSign := (if eqS then sa else isDN) in
    if uNaN ua || uNaN ub
    then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool (uSNaN ua || uSNaN ub)) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if uInf ua && uInf ub && negb eqS
    then (evalExpr (qnanE e f type) ,, (evalExpr (mkFlags type (ConstBool true) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) ,, tt))
    else if uInf ua then (a ,, (evalExpr (noFlags type) ,, tt))
    else if uInf ub then (b ,, (evalExpr (noFlags type) ,, tt))
    else if uZero ua && uZero ub then (evalExpr (zeroE e f type (ConstBool zzSign)) ,, (evalExpr (noFlags type) ,, tt))
    else if uZero ua then (b ,, (evalExpr (noFlags type) ,, tt))
    else if uZero ub then (a ,, (evalExpr (noFlags type) ,, tt))
    else addNrm rm (uSign ua) (uSign ub) (uExp ua) (uExp ub) (uSig ua) (uSig ub).

  Lemma addCore_V : forall rm a b ua ub, evalLetExpr (addCore false e f type rm a b ua ub) = addV rm a b ua ub.
  Proof. intros; exact eq_refl. Qed.

End Add.

(* The finite path: `alignAdd` then `normRound` is Flocq's rounding of the exact sum. *)
Section Nrm.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).
  Local Abbreviation XK := (Bit (e + 3)).
  Local Abbreviation fexpF := (SpecFloat.fexp (f + 1) (2 ^ (e - 1))).

  Lemma HeA : 2 <= e.
  Proof. exact (Glue.He e f Hf Hpe). Qed.

  Lemma normRound_zero : forall W s x (wsig : bits W) rm, Zmod.to_Z wsig = 0 ->
    evalLetExpr (normRound false e f type W s x wsig false rm) =
    (evalExpr (zeroE e f type (ConstBool s)) ,, (evalExpr (noFlags type) ,, tt)).
  Proof.
    intros W s x wsig rm H0.
    assert (Hw : wsig = Zmod.zero) by (apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; exact H0).
    subst wsig. unfold normRound; cbn [evalLetExpr]. cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault evalNot].
    rewrite isZero_eval, Zmod.unsigned_0. reflexivity.
  Qed.

  Lemma flags0 : forall m, finiteFlags (f + 1) (2 ^ (e - 1)) m 0%R = evalExpr (noFlags type).
  Proof.
    intros m. unfold finiteFlags, roundFlags. rewrite !round_0, !Rabs_R0.
    rewrite (Rlt_bool_true _ _ (bpow_gt_0 radix2 (2 ^ (e - 1)))).
    rewrite Req_bool_true by reflexivity. cbn [negb orb]. rewrite !andb_false_r. reflexivity.
    all: apply valid_rnd_round_mode.
  Qed.

  Definition nrmCore (rm : bits 3) (sB sS : bool) (xB xS : bits (e + 3)) (big sm : bits (f + 5)) : type (FpOutK e f) :=
    let al := evalLetExpr (alignAdd e type (f + 5) sB sS xB xS big sm) in
    let r := al.(Fst) in
    let st := al.(Snd).(Fst) in
    let xR := evalExpr (Add [Var type XK xB; cst (e + 3) 1]) in
    let sR := evalExpr (ITE (And [isZero (Var type (Bit (f + 5)) r); Not (Var type Bool st)])
                            (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) (Var type Bool sB)) in
    evalLetExpr (normRound false e f type (f + 5) sR xR r st rm).

  Lemma nrm_core : forall rm sB sS xB xS big sm SB SS XB XS v (Bres : binary_float (f + 1) (2 ^ (e - 1))),
    Zmod.signed xB = XB -> Zmod.signed xS = XS -> Zmod.to_Z big = 8 * SB -> Zmod.to_Z sm = 8 * SS ->
    2 ^ f <= SB < 2 ^ (f + 1) -> 2 ^ f <= SS < 2 ^ (f + 1) ->
    fpEmin e - f <= XB <= fpEmax e -> fpEmin e - f <= XS <= fpEmax e -> XS <= XB -> (XB = XS -> SS <= SB) ->
    v = (cond_Ropp sB (F2R (Float radix2 SB (XB - f))) + cond_Ropp sS (F2R (Float radix2 SS (XS - f))))%R ->
    (if Rlt_bool (Rabs (round radix2 fexpF (round_mode (modeOf rm)) v)) (bpow radix2 (2 ^ (e - 1)))
     then B2R Bres = round radix2 fexpF (round_mode (modeOf rm)) v /\ is_finite Bres = true /\
          Bsign Bres = (if Req_bool v 0 then Zmod.to_Z rm =? 2 else Rlt_bool v 0)
     else B2SF Bres = binary_overflow (f + 1) (2 ^ (e - 1)) (modeOf rm) sB) ->
    nrmCore rm sB sS xB xS big sm = (ofB Bres ,, (finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) v ,, tt)).
  Proof.
    intros rm sB sS xB xS big sm SB SS XB XS v Bres HXB HXS Hbig Hsm HSB HSS HRB HRS HXX HEq Hv HB.
    pose proof HeA as He.
    assert (Pe : 2 ^ (e + 2) = 8 * 2 ^ (e - 1)) by (replace (e + 2) with ((e - 1) + 3) by lia; rewrite Z.pow_add_r by lia; lia).
    assert (Pf4 : 2 ^ (f + 4) = 16 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    assert (Pf1 : 2 ^ (f + 1) = 2 * 2 ^ f) by (rewrite Z.pow_add_r by lia; lia).
    unfold fpEmin, fpEmax, fpBias in HRB, HRS.
    set (D := XB - XS).
    set (eS := negb (Bool.eqb sB sS)).
    destruct (add_int f Hf eS SB SS D HSB HSS ltac:(unfold D; lia) ltac:(unfold D; lia)) as (Hr & Hst & HN & Hrr & Hk).
    destruct (sh_eq f Hf SS D ltac:(lia) ltac:(unfold D; lia)) as [Q1 Q2].
    set (rZ := rAdd eS SB SS D) in *. set (stZ := stAdd SS D) in *.
    set (N := nAdd eS SB SS D) in *.
    destruct (alignAdd_vals e He (f + 5) sB sS xB xS big sm (8 * SB) (8 * SS) ltac:(lia) ltac:(lia) Hbig Hsm)
      as [Hal1 Hal2].
    { rewrite HXB, HXS; fold D; rewrite Q1, Q2; fold (stAdd SS D) stZ. fold eS.
      replace (if eS then 8 * SB - 8 * SS / 2 ^ D - b2z stZ else 8 * SB + 8 * SS / 2 ^ D) with rZ by reflexivity. exact Hrr. }
    rewrite HXB, HXS in Hal1, Hal2; fold D in Hal1, Hal2; rewrite Q1, Q2 in Hal1; rewrite Q2 in Hal2.
    fold (stAdd SS D) stZ eS in Hal1, Hal2.
    change (if eS then 8 * SB - 8 * SS / 2 ^ D - b2z stZ else 8 * SB + 8 * SS / 2 ^ D) with rZ in Hal1.
    unfold nrmCore; cbv zeta.
    set (al := evalLetExpr (alignAdd e type (f + 5) sB sS xB xS big sm)) in *.
    clearbody al. rewrite Hal2. set (r := Fst al) in *. clearbody r.
    set (xR := evalExpr (Add [Var type XK xB; cst (e + 3) 1])).
    assert (HxR : Zmod.signed xR = XB + 1).
    { unfold xR; cbn [evalExpr fold_left map evalBinary KindCustomInd getDefault cst].
      rewrite Zmod.add_0_l, <- (Zmod.of_Z_signed xB) at 1. rewrite <- Zmod.of_Z_add, HXB.
      apply signed_k; lia. }
    clearbody xR.
    set (sR := evalExpr (ITE (And [isZero (Var type (Bit (f + 5)) r); Not (Var type Bool stZ)])
                             (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) (Var type Bool sB))).
    assert (HsR : sR = if (rZ =? 0) && negb stZ then Zmod.to_Z rm =? 2 else sB).
    { unfold sR; cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault evalNot].
      rewrite isZero_eval, Hal1. cbn [isEq KindCustomInd evalExpr cst]. rewrite eqb_ofZ by (unfold RmRdn; cbn; lia). reflexivity. }
    clearbody sR.
    pose proof (bits.unsigned_range rm ltac:(lia)) as Hrm. change (2 ^ 3) with 8 in Hrm.
    (* the exact sum *)
    assert (HvN : v = cond_Ropp sB (F2R (Float radix2 N (XS - f - 3)))) by (rewrite Hv; unfold N, eS, D; apply sum_val; lia).
    assert (HP : 0 < 2 ^ D) by (apply Z.pow_pos_nonneg; unfold D; lia).
    pose proof (Z.div_mod N (2 ^ D) ltac:(lia)) as HdN. pose proof (Z.mod_pos_bound N (2 ^ D) HP) as HmN.
    rewrite <- Hr in HdN.
    assert (HabsV : Rabs v = F2R (Float radix2 N (XS - f - 3))).
    { rewrite HvN, abs_cond_Ropp. apply Rabs_pos_eq, F2R_nonneg; lia. }
    destruct (Z.eqb_spec rZ 0) as [Hr0 | Hr0].
    - (* exact cancellation *)
      assert (Hst0 : stZ = false) by (destruct stZ; [specialize (Hk eq_refl); pose proof (Z.pow_pos_nonneg 2 (f + 2)); lia | reflexivity]).
      rewrite Hst0 in HsR |- *. cbn [andb negb] in HsR.
      rewrite (normRound_zero (f + 5) sR xR r rm) by lia.
      assert (HN0 : N = 0).
      { rewrite Hst0 in Hst. destruct (Z.eqb_spec (N mod 2 ^ D) 0); [| discriminate]. lia. }
      assert (Hv0 : v = 0%R) by (rewrite HvN, HN0, F2R_0; destruct sB; cbn [cond_Ropp]; lra).
      rewrite Hv0 in HB |- *. rewrite round_0 in HB by apply valid_rnd_round_mode. rewrite Rabs_R0, Rlt_bool_true in HB by apply bpow_gt_0.
      rewrite Req_bool_true in HB by reflexivity. destruct HB as (HB1 & HB2 & HB3).
      assert (HBz : Bres = B754_zero (Zmod.to_Z rm =? 2)).
      { apply BinarySingleNaN.B2R_Bsign_inj; [exact HB2 | reflexivity | exact HB1 | exact HB3]. }
      rewrite HBz, HsR, ofB_zero, flags0 by exact Hpe. reflexivity.
    - (* non-zero sum *)
      replace (rZ =? 0) with false in HsR by (symmetry; apply Z.eqb_neq; exact Hr0). cbn [andb] in HsR. rewrite HsR.
      assert (Hrp : 0 < Zmod.to_Z r) by lia.
      pose proof (normRound_eval e f He Hf (f + 5) sB xR r stZ rm ltac:(lia) ltac:(lia) Hrp ltac:(lia)) as HNR.
      cbv zeta in HNR. rewrite HNR, Hal1, HxR.
      set (k := f + 5 - 1 - Z.log2 rZ).
      set (S := rZ * 2 ^ k / 2 ^ (f + 5 - (f + 3))).
      set (st2 := stZ || negb ((rZ * 2 ^ k) mod 2 ^ (f + 5 - (f + 3)) =? 0)).
      destruct (norm_window f Hf (f + 5) rZ ltac:(lia) ltac:(lia)) as (Hk1 & _ & HS); fold k S in Hk1, HS.
      pose proof (roundPack_Z e f He Hf Hpe sB (Zmod.of_Z (2 ^ (e + 3)) (XB + 1 - k)) (Zmod.of_Z (2 ^ (f + 3)) S) st2 rm) as HRP.
      cbv zeta in HRP. rewrite HRP. clear HRP HNR.
      rewrite (signed_k e He) by lia. rewrite (tz_ofZ (f + 3)) by lia.
      (* the location of the exact sum in the alignment window *)
      assert (Hin0 : exists l0, inbetween_float radix2 rZ (XB + 1 - (f + 5 - 1)) (Rabs v) l0 /\ (l0 = loc_Exact <-> stZ = false)).
      { destruct (Z.eq_dec D 0) as [HD0 | HD0].
        - exists loc_Exact. rewrite HD0, Z.pow_0_r, Z.div_1_r, Z.mod_1_r in *. split; [| split; [intros _ | reflexivity]].
          + constructor. rewrite HabsV, Hr. f_equal; f_equal; unfold D in HD0; lia.
          + exact Hst.
        - destruct (loc_shift (Rabs v) N (XS - f - 3) loc_Exact false D ltac:(unfold D in *; lia)) as [l' [H1 H2]].
          + constructor. exact HabsV.
          + split; [reflexivity | intros; reflexivity].
          + exists l'. rewrite <- Hr, <- Hst in *. split; [| exact H2].
            replace (XB + 1 - (f + 5 - 1)) with (XS - f - 3 + D) by (unfold D; lia). exact H1. }
      destruct Hin0 as (l0 & Hin & Hl0).
      assert (Hkd : stZ = true -> k <= f + 5 - (f + 3)).
      { intros Ht. specialize (Hk Ht). assert (f + 2 <= Z.log2 rZ) by (rewrite <- (Z.log2_pow2 (f + 2)) by lia; apply Z.log2_le_mono; exact Hk).
        unfold k; lia. }
      destruct (norm_loc f Hf (f + 5) rZ (XB + 1) stZ v l0 ltac:(lia) ltac:(lia) Hin Hl0 Hkd) as (l2 & Hin2 & Hl2).
      fold k S st2 in Hin2, Hl2.
      assert (HNpos : 0 < N) by nia.
      assert (Hs : Rlt_bool v 0 = sB).
      { rewrite HvN. assert (0 < F2R (Float radix2 N (XS - f - 3)))%R by (apply F2R_gt_0; exact HNpos).
        destruct sB; cbn [cond_Ropp]; [apply Rlt_bool_true; lra | apply Rlt_bool_false; lra]. }
      assert (Hv0 : Req_bool v 0 = false).
      { apply Req_bool_false. intros E0. rewrite E0 in Hs. rewrite Rlt_bool_false in Hs by lra.
        rewrite HvN, <- Hs in E0. cbn [cond_Ropp] in E0. assert (0 < F2R (Float radix2 N (XS - f - 3)))%R by (apply F2R_gt_0; exact HNpos). lra. }
      rewrite Hv0 in HB.
      assert (HB' : if Rlt_bool (Rabs (round radix2 fexpF (round_mode (modeZ (Zmod.to_Z rm))) v)) (bpow radix2 (2 ^ (e - 1)))
                    then B2R Bres = round radix2 fexpF (round_mode (modeZ (Zmod.to_Z rm))) v /\ is_finite Bres = true /\ Bsign Bres = sB
                    else B2SF Bres = binary_overflow (f + 1) (2 ^ (e - 1)) (modeZ (Zmod.to_Z rm)) sB).
      { change (modeZ (Zmod.to_Z rm)) with (modeOf rm). rewrite Hs in HB. exact HB. }
      pose proof (rp_result e f Hf Hpe (Zmod.to_Z rm) sB (XB + 1 - k) S st2 v l2 Hrm HS Hin2 Hl2 Hs Bres HB') as HT.
      pose proof (rp_flags e f Hf Hpe (Zmod.to_Z rm) sB (XB + 1 - k) S st2 v l2 Hrm HS Hin2 Hl2 Hs) as HF.
      f_equal; [| f_equal].
      + rewrite <- HT. symmetry; apply ofB_toB. rewrite HT, is_nan_B2SF by exact Hpe.
        destruct (Rlt_bool _ _) in HB'; [destruct HB' as (_ & HB2 & _); destruct Bres; easy |].
        rewrite HB'. unfold binary_overflow. destruct (overflow_to_inf _ _); reflexivity.
      + unfold finiteFlags. change (modeOf rm) with (modeZ (Zmod.to_Z rm)). rewrite HF. reflexivity.
  Qed.
End Nrm.

(* Choosing the larger operand. *)
Section Top.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).
  Local Abbreviation XK := (Bit (e + 3)).
  Local Abbreviation fexpF := (SpecFloat.fexp (f + 1) (2 ^ (e - 1))).

  Lemma big_val : forall c (x y : bits (f + 1)),
    Zmod.to_Z (evalExpr (Sll (zext (f + 1) (f + 5) (ITE (Var type Bool c) (Var type (Bit (f + 1)) x) (Var type (Bit (f + 1)) y))) (cst (f + 5) 3))) =
    8 * Zmod.to_Z (if c then x else y).
  Proof.
    intros c x y. cbn [evalExpr cst].
    assert (3 < 2 ^ (f + 5)) by (apply Z.lt_le_trans with (2 ^ 2); [cbn; lia | apply Z.pow_le_mono_r; lia]).
    rewrite bits.unsigned_slu, (tz_ofZ (f + 5) 3), Z.shiftl_mul_pow2, unsigned_zext by lia. cbn [evalExpr].
    change (2 ^ 3) with 8.
    assert (Hp : 2 ^ (f + 5) = 2 ^ (f + 1) * 16) by (replace (f + 5) with ((f + 1) + 4) by lia; rewrite Z.pow_add_r by lia; reflexivity).
    destruct c; [pose proof (bits.unsigned_range x ltac:(lia)) | pose proof (bits.unsigned_range y ltac:(lia))];
      rewrite Z.mul_comm; apply Z.mod_small; lia.
  Qed.

  Lemma eqbits_signed : forall (x y : bits (e + 3)), Zmod.eqb x y = (Zmod.signed x =? Zmod.signed y).
  Proof.
    intros x y. destruct (Zmod.eqb_spec x y) as [-> | Hn]; [symmetry; apply Z.eqb_refl |].
    symmetry; apply Z.eqb_neq; intros E; apply Hn, Zmod.signed_inj, E.
  Qed.

  Lemma addNrm_nrm : forall rm sa sb xa xb siga sigb,
    addNrm e f rm sa sb xa xb siga sigb =
    let aBig := evalExpr (Or [Var type Bool (evalExpr (Slt (Var type XK xb) (Var type XK xa)));
                              And [Var type Bool (evalExpr (Eq (Var type XK xa) (Var type XK xb)));
                                   Not (Ult (Var type (Bit (f + 1)) siga) (Var type (Bit (f + 1)) sigb))]]) in
    nrmCore e f rm (if aBig then sa else sb) (if aBig then sb else sa) (if aBig then xa else xb) (if aBig then xb else xa)
      (evalExpr (Sll (zext (f + 1) (f + 5) (ITE (Var type Bool aBig) (Var type (Bit (f + 1)) siga) (Var type (Bit (f + 1)) sigb))) (cst (f + 5) 3)))
      (evalExpr (Sll (zext (f + 1) (f + 5) (ITE (Var type Bool aBig) (Var type (Bit (f + 1)) sigb) (Var type (Bit (f + 1)) siga))) (cst (f + 5) 3))).
  Proof. intros; reflexivity. Qed.

  Lemma addNrm_spec : forall rm sa sb xa xb siga sigb Sa Sb Xa Xb v (Bres : binary_float (f + 1) (2 ^ (e - 1))),
    Zmod.signed xa = Xa -> Zmod.signed xb = Xb -> Zmod.to_Z siga = Sa -> Zmod.to_Z sigb = Sb ->
    2 ^ f <= Sa < 2 ^ (f + 1) -> 2 ^ f <= Sb < 2 ^ (f + 1) ->
    fpEmin e - f <= Xa <= fpEmax e -> fpEmin e - f <= Xb <= fpEmax e ->
    v = (cond_Ropp sa (F2R (Float radix2 Sa (Xa - f))) + cond_Ropp sb (F2R (Float radix2 Sb (Xb - f))))%R ->
    (if Rlt_bool (Rabs (round radix2 fexpF (round_mode (modeOf rm)) v)) (bpow radix2 (2 ^ (e - 1)))
     then B2R Bres = round radix2 fexpF (round_mode (modeOf rm)) v /\ is_finite Bres = true /\
          Bsign Bres = (if Req_bool v 0 then Zmod.to_Z rm =? 2 else Rlt_bool v 0)
     else B2SF Bres = binary_overflow (f + 1) (2 ^ (e - 1)) (modeOf rm) sa /\ sa = sb) ->
    addNrm e f rm sa sb xa xb siga sigb = (ofB Bres ,, (finiteFlags (f + 1) (2 ^ (e - 1)) (modeOf rm) v ,, tt)).
  Proof.
    intros rm sa sb xa xb siga sigb Sa Sb Xa Xb v Bres HXa HXb HSa HSb RSa RSb RXa RXb Hv HB.
    pose proof (HeA e f Hf Hpe) as He.
    rewrite addNrm_nrm; cbv zeta.
    match goal with |- context [nrmCore e f rm (if ?c then _ else _)] => set (aB := c) end.
    assert (HaB : aB = (Xb <? Xa) || ((Xa =? Xb) && negb (Sa <? Sb))).
    { unfold aB; cbn [evalExpr fold_left map evalOrBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault evalNot isEq].
      rewrite slt_eval by lia; cbn [evalExpr]. rewrite eqbits_signed, HXa, HXb, HSa, HSb. reflexivity. }
    clearbody aB.
    destruct aB.
    - eapply (nrm_core e f Hf Hpe) with (SB := Sa) (SS := Sb) (XB := Xa) (XS := Xb); try eassumption.
      + rewrite big_val; cbn iota; congruence.
      + rewrite big_val; cbn iota; congruence.
      + destruct (Z.ltb_spec Xb Xa); destruct (Z.eqb_spec Xa Xb); destruct (Z.ltb_spec Sa Sb); cbn in HaB; try discriminate; lia.
      + intros ?. destruct (Z.ltb_spec Xb Xa); destruct (Z.eqb_spec Xa Xb); destruct (Z.ltb_spec Sa Sb); cbn in HaB; try discriminate; lia.
      + destruct (Rlt_bool _ _); [exact HB | apply HB].
    - eapply (nrm_core e f Hf Hpe) with (SB := Sb) (SS := Sa) (XB := Xb) (XS := Xa); try eassumption.
      + rewrite big_val; cbn iota; congruence.
      + rewrite big_val; cbn iota; congruence.
      + destruct (Z.ltb_spec Xb Xa); destruct (Z.eqb_spec Xa Xb); destruct (Z.ltb_spec Sa Sb); cbn in HaB; try discriminate; lia.
      + intros E. destruct (Z.ltb_spec Xb Xa); destruct (Z.eqb_spec Xa Xb); destruct (Z.ltb_spec Sa Sb); cbn in HaB; try discriminate; lia.
      + rewrite Hv; apply Rplus_comm.
      + destruct (Rlt_bool _ _); [exact HB | destruct HB as [HB1 HB2]; rewrite <- HB2; exact HB1].
  Qed.
End Top.

(* `addCore` against `Bplus`, all operand classes. *)
Section Main.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).
  Local Abbreviation unp := (fun x => evalLetExpr (fpUnpack false e f type x)).
  Local Instance pgM : FLX.Prec_gt_0 (f + 1) := prec_gt_0 e f Hf.
  Local Instance plM : Prec_lt_emax (f + 1) (2 ^ (e - 1)) := prec_lt_emax e f Hpe.

  Lemma mkFlags_eval : forall nv,
    evalExpr (mkFlags type (ConstBool nv) (ConstBool false) (ConstBool false) (ConstBool false) (ConstBool false)) =
    mkFl nv false false false false.
  Proof. intros []; reflexivity. Qed.

  Lemma noFlags_eval : evalExpr (noFlags type) = mkFl false false false false false.
  Proof. reflexivity. Qed.

  Lemma eqS_eval : forall x y : bool, evalExpr (Eq (Var type Bool x) (Var type Bool y)) = Bool.eqb x y.
  Proof. reflexivity. Qed.

  Lemma isDN_eval : forall rm : bits 3, evalExpr (Eq (Var type (Bit 3) rm) (cst 3 RmRdn)) = (Zmod.to_Z rm =? 2).
  Proof. intros rm; cbn [evalExpr isEq KindCustomInd cst]. apply eqb_ofZ; unfold RmRdn; cbn; lia. Qed.

  Lemma dnZ : forall rm : bits 3, (match modeOf rm with mode_DN => true | _ => false end) = (Zmod.to_Z rm =? 2).
  Proof.
    intros rm. change (modeOf rm) with (modeZ (Zmod.to_Z rm)).
    assert (H : 0 <= Zmod.to_Z rm < 8) by (pose proof (bits.unsigned_range rm ltac:(lia)) as H; exact H).
    generalize (Zmod.to_Z rm) H; intros z Hz.
    destruct (rm_cases _ Hz) as [E | [E | [E | [E | [E | [E | [E | E]]]]]]]; subst z; reflexivity.
  Qed.

  Lemma zero_DN : forall rm : bits 3,
    (match modeOf rm with mode_DN => @B754_zero (f + 1) (2 ^ (e - 1)) true | _ => B754_zero false end) =
    B754_zero (Zmod.to_Z rm =? 2).
  Proof. intros rm; rewrite <- dnZ; destruct (modeOf rm); reflexivity. Qed.

  Lemma sign_ok : forall (rm : bits 3) sa sb x y, (0 < x)%R -> (0 < y)%R ->
    match Rcompare (cond_Ropp sa x + cond_Ropp sb y) 0 with
    | Datatypes.Eq => match modeOf rm with mode_DN => sa || sb | _ => sa && sb end
    | Datatypes.Lt => true | Datatypes.Gt => false end =
    (if Req_bool (cond_Ropp sa x + cond_Ropp sb y) 0 then Zmod.to_Z rm =? 2 else Rlt_bool (cond_Ropp sa x + cond_Ropp sb y) 0).
  Proof.
    intros rm sa sb x y Hx Hy.
    destruct (Rcompare_spec (cond_Ropp sa x + cond_Ropp sb y) 0) as [H | H | H].
    - rewrite Req_bool_false, Rlt_bool_true by lra; reflexivity.
    - rewrite Req_bool_true by exact H. rewrite <- dnZ.
      destruct sa, sb; cbn [cond_Ropp] in H; try lra; destruct (modeOf rm); reflexivity.
    - rewrite Req_bool_false, Rlt_bool_false by lra; reflexivity.
  Qed.

  Definition zB (E M : Z) : bool := (E =? 0) && (M =? 0).
  Definition iB (E M : Z) : bool := (E =? 2 ^ e - 1) && (M =? 0).
  Definition nB (E M : Z) : bool := (E =? 2 ^ e - 1) && negb (M =? 0).

  Lemma cls_bools : forall (x : binary_float (f + 1) (2 ^ (e - 1))) s E M, clsP e f x s E M ->
    match x with
    | B754_zero s' => s' = s /\ zB E M = true /\ iB E M = false /\ nB E M = false
    | B754_infinity s' => s' = s /\ zB E M = false /\ iB E M = true /\ nB E M = false
    | B754_nan => zB E M = false /\ iB E M = false /\ nB E M = true
    | B754_finite s' _ _ _ => s' = s /\ zB E M = false /\ iB E M = false /\ nB E M = false /\
                              E <> 2 ^ e - 1 /\ (E <> 0 \/ M <> 0)
    end.
  Proof.
    intros x s E M C. pose proof (HeA e f Hf Hpe).
    assert (He4 : 4 <= 2 ^ e) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia).
    unfold zB, iB, nB.
    destruct x as [s' | s' | | s' m ex Hb]; cbn [clsP] in C.
    - destruct C as (-> & -> & ->). rewrite Z.eqb_refl. replace (0 =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia). auto.
    - destruct C as (-> & -> & ->). rewrite !Z.eqb_refl. replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). auto.
    - destruct C as (-> & HM). rewrite Z.eqb_refl. replace (2 ^ e - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (M =? 0) with false by (symmetry; apply Z.eqb_neq; lia). auto.
    - destruct C as (-> & H1 & H2 & _). replace (E =? 2 ^ e - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [reflexivity |]. split; [| repeat split; auto].
      destruct (Z.eqb_spec E 0), (Z.eqb_spec M 0); cbn; try reflexivity; lia.
  Qed.

  Theorem add_main : forall rm a b,
    addV e f rm a b (unp a) (unp b) =
    (ofB (BinarySingleNaN.Bplus (modeOf rm) (toB a) (toB b)) ,, (addFlags e f Hf Hpe rm a b ,, tt)).
  Proof.
    intros rm a b. pose proof (HeA e f Hf Hpe) as He.
    destruct (split_fields e f Hf Hpe a) as (sa & Ea & Ma & HMa & HEa & Ha).
    destruct (split_fields e f Hf Hpe b) as (sb & Eb & Mb & HMb & HEb & Hb).
    pose proof (cls_bools _ _ _ _ (cls e f Hf Hpe a sa Ea Ma HMa HEa Ha)) as Ka.
    pose proof (cls_bools _ _ _ _ (cls e f Hf Hpe b sb Eb Mb HMb HEb Hb)) as Kb.
    unfold addV, addFlags; cbv beta zeta.
    rewrite (u_sign e f He Hf a sa Ea Ma HMa HEa Ha), (u_sign e f He Hf b sb Eb Mb HMb HEb Hb).
    rewrite (u_zero e f He Hf a sa Ea Ma HMa HEa Ha), (u_zero e f He Hf b sb Eb Mb HMb HEb Hb).
    rewrite (u_inf e f He Hf a sa Ea Ma HMa HEa Ha), (u_inf e f He Hf b sb Eb Mb HMb HEb Hb).
    rewrite (u_snan e f He Hf a sa Ea Ma HMa HEa Ha), (u_snan e f He Hf b sb Eb Mb HMb HEb Hb).
    rewrite (u_nan e f He Hf a sa Ea Ma HMa HEa Ha), (u_nan e f He Hf b sb Eb Mb HMb HEb Hb).
    rewrite (isSNaN_eq e f Hf Hpe a sa Ea Ma HMa HEa Ha), (isSNaN_eq e f Hf Hpe b sb Eb Mb HMb HEb Hb).
    rewrite eqS_eval, isDN_eval, mkFlags_eval, mkFlags_eval, noFlags_eval.
    fold (zB Ea Ma) (zB Eb Mb) (iB Ea Ma) (iB Eb Mb) (nB Ea Ma) (nB Eb Mb).
    destruct (toB a) as [sa' | sa' | | sa' ma ea Hba] eqn:TA;
      destruct (toB b) as [sb' | sb' | | sb' mb eb Hbb] eqn:TB;
      repeat match goal with
             | H : _ = _ /\ _ |- _ => destruct H
             | H : _ <> _ /\ _ |- _ => destruct H end; subst;
      repeat match goal with H : ?x = _ |- _ => (rewrite H; clear H) end; cbn [orb andb negb].
    (* 1: zero + zero *)
    - destruct sa, sb; cbn [BinarySingleNaN.Bplus Bool.eqb]; try rewrite zero_DN; rewrite (ofB_zero e f Hf Hpe); reflexivity.
    (* 2: zero + inf *)
    - cbn [BinarySingleNaN.Bplus]. rewrite <- TB, (ofB_toB e f Hf Hpe b) by (rewrite TB; reflexivity). reflexivity.
    (* 3: zero + nan *)
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    (* 4: zero + finite *)
    - cbn [BinarySingleNaN.Bplus]. rewrite <- TB, (ofB_toB e f Hf Hpe b) by (rewrite TB; reflexivity). reflexivity.
    (* 5: inf + zero *)
    - cbn [BinarySingleNaN.Bplus]. rewrite <- TA, (ofB_toB e f Hf Hpe a) by (rewrite TA; reflexivity). reflexivity.
    (* 6: inf + inf *)
    - destruct sa, sb; cbn [BinarySingleNaN.Bplus Bool.eqb negb];
        first [rewrite (ofB_nan e f Hf Hpe); reflexivity | rewrite <- TA, (ofB_toB e f Hf Hpe a) by (rewrite TA; reflexivity); reflexivity].
    (* 7: inf + nan *)
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    (* 8: inf + finite *)
    - cbn [BinarySingleNaN.Bplus]. rewrite <- TA, (ofB_toB e f Hf Hpe a) by (rewrite TA; reflexivity). reflexivity.
    (* 9 - 12: nan + _ *)
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    (* 13: finite + zero *)
    - cbn [BinarySingleNaN.Bplus]. rewrite <- TA, (ofB_toB e f Hf Hpe a) by (rewrite TA; reflexivity). reflexivity.
    (* 14: finite + inf *)
    - cbn [BinarySingleNaN.Bplus]. rewrite <- TB, (ofB_toB e f Hf Hpe b) by (rewrite TB; reflexivity). reflexivity.
    (* 15: finite + nan *)
    - cbn [BinarySingleNaN.Bplus]. rewrite (ofB_nan e f Hf Hpe). reflexivity.
    (* 16: finite + finite *)
    - rewrite <- TA, <- TB.
      pose proof (fin_facts e f Hf Hpe a sa Ea Ma HMa HEa Ha ltac:(assumption) ltac:(assumption)) as FA.
      pose proof (fin_facts e f Hf Hpe b sb Eb Mb HMb HEb Hb ltac:(assumption) ltac:(assumption)) as FB.
      cbv zeta in FA, FB. destruct FA as (RSa & RXa & HRa & Fa & Sga). destruct FB as (RSb & RXb & HRb & Fb & Sgb).
      pose proof (BinarySingleNaN.Bplus_correct (f + 1) (2 ^ (e - 1)) _ _ (modeOf rm) (toB a) (toB b) Fa Fb) as BC.
      rewrite Sga, Sgb in BC.
      apply (addNrm_spec e f Hf Hpe rm sa sb _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl RSa RSb RXa RXb).
      + rewrite HRa, HRb; reflexivity.
      + destruct (Rlt_bool _ _); [| exact BC].
        destruct BC as (B1 & B2 & B3). split; [exact B1 |]. split; [exact B2 |]. rewrite B3, HRa, HRb.
        apply sign_ok; apply F2R_gt_0; cbn [Fnum]; lia.
  Qed.
End Main.

(* FSUB: the sign flip of `b` is Flocq's `Bopp`. *)
Section Flip.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation isSN := (isSNaN e f Hf Hpe).

  Lemma flipF : forall b : bits W, evalExpr (flipSign e f type (And [ConstBool true; ConstBool false]) b) = b.
  Proof.
    intros b; pose proof (Glue.He e f Hf Hpe).
    cbn [evalExpr flipSign fold_left map evalXorBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault andb cst].
    change (Zmod.xor (Zmod.xor Zmod.zero b) (Zmod.of_Z (2 ^ W) 0) = b). apply Zmod.unsigned_inj.
    rewrite !bits.unsigned_xor, Zmod.unsigned_0, Z.lxor_0_l, Zmod.unsigned_of_Z, Z.mod_0_l, Z.lxor_0_r
      by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.

  Definition negBits (b : bits W) : bits W := evalExpr (flipSign e f type (And [ConstBool true; ConstBool true]) b).

  Lemma negBits_fields : forall (b : bits W) s E M, 0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z b = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    Zmod.to_Z (negBits b) = b2z (negb s) * 2 ^ (f + e) + E * 2 ^ f + M.
  Proof.
    intros b s E M HM HE Hb. pose proof (Glue.He e f Hf Hpe).
    unfold negBits.
    cbn [evalExpr flipSign fold_left map evalXorBinary evalAndBinary evalBinary KindCustomInd getDefault InvDefault andb cst].
    change (Zmod.to_Z (Zmod.xor (Zmod.xor Zmod.zero b) (Zmod.of_Z (2 ^ W) (2 ^ (f + e)))) = b2z (negb s) * 2 ^ (f + e) + E * 2 ^ f + M).
    rewrite bits_xor_0_l.
    assert (Hc : Zmod.of_Z (2 ^ W) (2 ^ (f + e)) = Zmod.of_Z (2 ^ W) (2 ^ (W - 1))) by (do 2 f_equal; lia).
    rewrite Hc, xor_top by lia.
    assert (HW : 2 ^ W = 2 * 2 ^ (f + e)) by (rewrite Z.pow_add_r by lia; lia).
    assert (HW1 : 2 ^ (W - 1) = 2 ^ (f + e)) by (f_equal; lia).
    assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; lia).
    assert (0 <= E * 2 ^ f) by (apply Z.mul_nonneg_nonneg; lia).
    assert (E * 2 ^ f + M < 2 ^ (f + e)) by (assert (E * 2 ^ f <= (2 ^ e - 1) * 2 ^ f) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
    rewrite HW1. destruct s; cbn [b2z negb] in *.
    - rewrite Zmod.signed_large by lia. rewrite Hb, HW. lia.
    - rewrite Zmod.signed_small by lia. rewrite Hb. lia.
  Qed.

  Lemma B2SF_Bopp : forall x : binary_float (f + 1) (2 ^ (e - 1)),
    B2SF (Bopp x) = match B2SF x with
                    | S754_zero s => S754_zero (negb s) | S754_infinity s => S754_infinity (negb s)
                    | S754_nan => S754_nan | S754_finite s m ex => S754_finite (negb s) m ex end.
  Proof. intros [| | |]; reflexivity. Qed.

  Lemma toB_negBits : forall b : bits W, toB (negBits b) = Bopp (toB b).
  Proof.
    intros b. destruct (split_fields e f Hf Hpe b) as (s & E & M & HM & HE & Hb).
    apply B2SF_inj. rewrite B2SF_Bopp.
    rewrite (B2SF_toB_fields e f Hf Hpe (negBits b) (negb s) E M HM HE (negBits_fields b s E M HM HE Hb)).
    rewrite (B2SF_toB_fields e f Hf Hpe b s E M HM HE Hb).
    unfold sfFields. destruct (E =? 0), (M =? 0), (E =? 2 ^ e - 1); reflexivity.
  Qed.

  Lemma isSN_negBits : forall b : bits W, isSN (negBits b) = isSN b.
  Proof.
    intros b. destruct (split_fields e f Hf Hpe b) as (s & E & M & HM & HE & Hb).
    rewrite (isSNaN_eq e f Hf Hpe (negBits b) (negb s) E M HM HE (negBits_fields b s E M HM HE Hb)).
    rewrite (isSNaN_eq e f Hf Hpe b s E M HM HE Hb). reflexivity.
  Qed.

  Lemma subFlags_add : forall rm a b, subFlags e f Hf Hpe rm a b = addFlags e f Hf Hpe rm a (negBits b).
  Proof.
    intros rm a b. unfold subFlags, addFlags. rewrite toB_negBits, isSN_negBits, B2R_Bopp.
    destruct (toB a), (toB b); cbn [Bopp]; try reflexivity.
    - destruct s, s0; reflexivity.
  Qed.

  Lemma Bminus_Bplus : forall m (x y : binary_float (f + 1) (2 ^ (e - 1))),
    @Bminus (f + 1) (2 ^ (e - 1)) (prec_gt_0 e f Hf) (prec_lt_emax e f Hpe) m x y =
    @Bplus (f + 1) (2 ^ (e - 1)) (prec_gt_0 e f Hf) (prec_lt_emax e f Hpe) m x (Bopp y).
  Proof. intros m [| | |] [| | |]; reflexivity. Qed.
End Flip.

(* ---------------------------------------------------------------------------
 * The reference core on FADD / FSUB is `addCore`
 * --------------------------------------------------------------------------- *)

Section Final.
  Variable e f xlen wlen : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation W := (f + e + 1).

  Lemma pipe_info : forall negB rm a b,
    evalLetExpr (pipeInfoOf false e f xlen type (reqA e f xlen (opAdd negB) rm a b Zmod.zero Zmod.zero)) =
    (opAdd negB ,, (Zmod.zero ,, (rm ,, (a ,, (evalExpr (flipSign e f type (And [ConstBool true; ConstBool negB]) b) ,,
      (evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) Zmod.zero) ,,
      (evalLetExpr (fpUnpack false e f type a) ,,
      (evalLetExpr (fpUnpack false e f type (evalExpr (flipSign e f type (And [ConstBool true; ConstBool negB]) b))) ,,
      (evalLetExpr (fpUnpack false e f type (evalExpr (flipSign e f type (And [ConstBool false; ConstBool false]) Zmod.zero))) ,,
      (false ,, tt)))))))))).
  Proof. intros; exact eq_refl. Qed.

  Lemma pipe_finish_res : forall negB (x : bits xlen) rm a b2 c2 ua ub uc np prod,
    (evalLetExpr (pipeFinishCore false e f xlen wlen type
       (opAdd negB ,, (x ,, (rm ,, (a ,, (b2 ,, (c2 ,, (ua ,, (ub ,, (uc ,, (np ,, tt)))))))))) prod)) @% "res" =
    (evalLetExpr (addCore false e f type rm a b2 ua ub)).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma pipe_finish_flags : forall negB (x : bits xlen) rm a b2 c2 ua ub uc np prod,
    (evalLetExpr (pipeFinishCore false e f xlen wlen type
       (opAdd negB ,, (x ,, (rm ,, (a ,, (b2 ,, (c2 ,, (ua ,, (ub ,, (uc ,, (np ,, tt)))))))))) prod)) @% "flags" =
    (evalLetExpr (addCore false e f type rm a b2 ua ub)).(Snd).(Fst).
  Proof. intros; exact eq_refl. Qed.

  Lemma compute_pipe : forall negB rm a b,
    evalLetExpr (fpuComputeRef e f xlen wlen type (reqA e f xlen (opAdd negB) rm a b Zmod.zero Zmod.zero)) =
    evalLetExpr (pipeSpec false e f xlen wlen type (reqA e f xlen (opAdd negB) rm a b Zmod.zero Zmod.zero)).
  Proof. intros; exact eq_refl. Qed.

  Lemma core_res : forall negB rm a b,
    (evalLetExpr (fpuComputeRef e f xlen wlen type (reqA e f xlen (opAdd negB) rm a b Zmod.zero Zmod.zero))) @% "res" =
    (addCoreT e f negB rm a b).(Fst).
  Proof. intros. rewrite compute_pipe. unfold pipeSpec. cbn [evalLetExpr]. rewrite pipe_info. apply pipe_finish_res. Qed.

  Lemma core_flags : forall negB rm a b,
    (evalLetExpr (fpuComputeRef e f xlen wlen type (reqA e f xlen (opAdd negB) rm a b Zmod.zero Zmod.zero))) @% "flags" =
    (addCoreT e f negB rm a b).(Snd).(Fst).
  Proof. intros. rewrite compute_pipe. unfold pipeSpec. cbn [evalLetExpr]. rewrite pipe_info. apply pipe_finish_flags. Qed.

  Theorem fadd_flocq_holds : fadd_flocq e f xlen wlen Hf Hpe.
  Proof.
    intros rm a b. unfold faddRef. rewrite core_res, core_flags. unfold addCoreT; cbv beta zeta.
    rewrite (flipF e f Hf Hpe b), addCore_V.
    pose proof (add_main e f Hf Hpe rm a b) as HM; cbv beta in HM. rewrite HM. split; reflexivity.
  Qed.

  Theorem fsub_flocq_holds : fsub_flocq e f xlen wlen Hf Hpe.
  Proof.
    intros rm a b. unfold fsubRef. rewrite core_res, core_flags. unfold addCoreT; cbv beta zeta.
    change (evalExpr (flipSign e f type (And [ConstBool true; ConstBool true]) b)) with (negBits e f b).
    rewrite addCore_V.
    pose proof (add_main e f Hf Hpe rm a (negBits e f b)) as HM; cbv beta in HM. rewrite HM. cbn [Fst Snd].
    rewrite (toB_negBits e f Hf Hpe b), (subFlags_add e f Hf Hpe). split; [| reflexivity].
    rewrite (Bminus_Bplus e f Hf Hpe). reflexivity.
  Qed.
End Final.
