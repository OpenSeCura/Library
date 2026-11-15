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
 * Rounding by location (`RoundLoc.v`): the guard / round-sticky view of rounding used by
 * `FpCore`, connected to Flocq's `inbetween_float` locations and its rounding functions.
 *
 * - `loc_drop2`, `loc_shift`: dropping low significand bits updates the location;
 * - `round_at`: with the location given by the guard bit `g` and the round-sticky bit `r`,
 *   Flocq's rounding (any mode, any valid exponent function) is the truncated significand plus
 *   `FpCore`'s round-up decision `rmInc`.
 *)

From Stdlib Require Import ZArith Reals Lia Bool.
From Flocq Require Import Core.Core Calc.Bracket Calc.Round IEEE754.BinarySingleNaN.
From Fpu.FlocqProof Require Import Flags RoundBits.

Local Open Scope Z_scope.

(* The location of a value from the guard bit and the round-sticky bit. *)
Definition locOf (g r : bool) : location :=
  if g then loc_Inexact (if r then Gt else Eq) else (if r then loc_Inexact Lt else loc_Exact).

(* Flocq's mode of an integer RISC-V rounding mode (5..7 behave as RNE, like `FpCore`). *)
Definition modeZ (rmz : Z) : mode :=
  match rmz with 1 => mode_ZR | 2 => mode_DN | 3 => mode_UP | 4 => mode_NA | _ => mode_NE end.

Lemma testbit_mod4 : forall M i, 0 <= i < 2 -> Z.testbit M i = Z.testbit (M mod 4) i.
Proof. intros M i Hi; change 4 with (2 ^ 2); rewrite Z.mod_pow2_bits_low by lia; reflexivity. Qed.

(* Dropping the two low bits. *)
Lemma loc_drop2 : forall x M ex l st,
  inbetween_float radix2 M ex x l -> (l = loc_Exact <-> st = false) ->
  inbetween_float radix2 (M / 4) (ex + 2) x (locOf (Z.testbit M 1) (Z.testbit M 0 || st)).
Proof.
  intros x M ex l st Hin Hl.
  pose proof (inbetween_float_new_location radix2 x M ex l 2 ltac:(lia) Hin) as H.
  change (Zpower radix2 2) with 4 in H.
  replace (locOf (Z.testbit M 1) (Z.testbit M 0 || st)) with (new_location 4 (M mod 4) l); [exact H |].
  rewrite (testbit_mod4 M 1), (testbit_mod4 M 0) by lia.
  unfold new_location, new_location_even; cbn [Z.even].
  assert (Hm : M mod 4 = 0 \/ M mod 4 = 1 \/ M mod 4 = 2 \/ M mod 4 = 3) by (pose proof (Z.mod_pos_bound M 4); lia).
  destruct Hm as [-> | [-> | [-> | ->]]]; cbn;
    destruct l; destruct st; try reflexivity; destruct Hl as [H1 H2];
    (discriminate (H2 eq_refl) || discriminate (H1 eq_refl)).
Qed.

(* Dropping `d > 0` low bits into the sticky bit. *)
Lemma loc_shift : forall x M ex l st d, 0 < d ->
  inbetween_float radix2 M ex x l -> (l = loc_Exact <-> st = false) ->
  exists l', inbetween_float radix2 (M / 2 ^ d) (ex + d) x l' /\
             (l' = loc_Exact <-> (st || negb (M mod 2 ^ d =? 0)) = false).
Proof.
  intros x M ex l st d Hd Hin Hl.
  pose proof (inbetween_float_new_location radix2 x M ex l d Hd Hin) as H.
  change (Zpower radix2 d) with (2 ^ d) in H.
  eexists; split; [exact H |].
  unfold new_location.
  replace (Z.even (2 ^ d)) with true by (rewrite Z.even_pow by lia; reflexivity).
  unfold new_location_even.
  destruct (Z.eqb_spec (M mod 2 ^ d) 0) as [E | E]; cbn [negb]; rewrite ?orb_false_r, ?orb_true_r.
  - destruct l; [exact Hl |]. split; [discriminate |]; intros ->; destruct Hl as [_ Hl']; discriminate (Hl' eq_refl).
  - split; discriminate.
Qed.

Lemma rm_cases : forall rmz, 0 <= rmz < 8 ->
  rmz = 0 \/ rmz = 1 \/ rmz = 2 \/ rmz = 3 \/ rmz = 4 \/ rmz = 5 \/ rmz = 6 \/ rmz = 7.
Proof. intros; lia. Qed.

(* Rounding from the guard / round-sticky location. *)
Lemma round_at : forall (fexp : Z -> Z) {Hv : Valid_exp fexp} rmz s v m ex g r,
  0 <= rmz < 8 -> Rlt_bool v 0 = s ->
  cexp radix2 fexp v = ex ->
  inbetween_float radix2 m ex (Rabs v) (locOf g r) ->
  round radix2 fexp (round_mode (modeZ rmz)) v =
  F2R (Float radix2 (cond_Zopp s (m + b2z (rmInc rmz s (negb (Z.even m)) g r))) ex).
Proof.
  intros fexp Hv rmz s v m ex g r Hrm Hs Hc Hin; subst ex.
  destruct (rm_cases rmz Hrm) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn [modeZ round_mode];
    [ rewrite (inbetween_float_NE_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_ZR_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_DN_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_UP_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_NA_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_NE_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_NE_sign radix2 fexp v m _ Hin)
    | rewrite (inbetween_float_NE_sign radix2 fexp v m _ Hin) ];
    rewrite Hs; do 3 f_equal; unfold rmInc, rneZ, cond_incr; cbn [Z.eqb Z.ltb Z.compare negb orb andb];
    destruct g, r, s, (Z.even m); cbn; lia.
Qed.
