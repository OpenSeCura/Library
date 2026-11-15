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
 * Decoding bit patterns into Flocq floats, field by field (`Decode.v`).
 *
 * `B2SF (toB x)` is computed from the sign / exponent-field / fraction-field split of `x`
 * (`sfFields`), and `ofB (toB x) = x` for every non-NaN pattern.
 *)

From Stdlib Require Import ZArith Zmod Zmod.Bits Lia Reals.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Zaux Core.Defs Core.Digits IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives.
From Fpu.FlocqProof Require Import Glue Flags.

Local Open Scope Z_scope.

Section Decode.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation prec := (f + 1).
  Local Abbreviation emax := (2 ^ (e - 1)).
  Local Abbreviation W := (f + e + 1).
  Local Abbreviation toB := (toB e f Hf Hpe).
  Local Abbreviation toBp := (toBp e f Hf Hpe).
  Local Abbreviation ofB := (ofB e f Hf).

  Lemma He' : 2 <= e.
  Proof. exact (He e f Hf Hpe). Qed.

  (* The float of the fields: sign `s`, exponent field `E`, fraction field `M`. *)
  Definition sfFields (s : bool) (E M : Z) : spec_float :=
    if E =? 0 then (if M =? 0 then S754_zero s else S754_finite s (Z.to_pos M) (SpecFloat.emin prec emax))
    else if E =? 2 ^ e - 1 then (if M =? 0 then S754_infinity s else S754_nan)
    else S754_finite s (Z.to_pos (M + 2 ^ f)) (E + SpecFloat.emin prec emax - 1).

  Lemma join_bits_eq : forall s E M,
    join_bits f e s M E = b2z s * 2 ^ (f + e) + E * 2 ^ f + M.
  Proof.
    intros s E M; pose proof He'; unfold join_bits; rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.pow_add_r by lia; destruct s; cbn [b2z]; ring.
  Qed.

  Lemma B2SF_toB_fields : forall (x : bits W) s E M,
    0 <= M < 2 ^ f -> 0 <= E < 2 ^ e ->
    Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M ->
    BinarySingleNaN.B2SF (toB x) = sfFields s E M.
  Proof.
    intros x s E M HM HE Hx; pose proof He'.
    unfold Glue.toB, Glue.toBp; rewrite B2SF_B2BSN; unfold binary_float_of_bits; rewrite B2SF_FF2B.
    rewrite Hx, <- join_bits_eq; unfold binary_float_of_bits_aux; rewrite split_join_bits by lia.
    unfold sfFields.
    destruct (Z.eqb_spec E 0) as [HE0 | HE0].
    -
      destruct (Z.eqb_spec M 0) as [-> | HM0]; [reflexivity |].
      destruct M as [| p | p]; [lia | reflexivity | lia].
    -
      destruct (Z.eqb_spec E (2 ^ e - 1)) as [HE1 | HE1].
      +
        destruct (Z.eqb_spec M 0) as [-> | HM0]; [reflexivity |].
        destruct M as [| p | p]; [lia | reflexivity | lia].
      +
        assert (Hp : 0 < M + 2 ^ f) by lia.
        destruct (M + 2 ^ f) as [| p | p]; [lia | reflexivity | lia].
  Qed.

  (* Every pattern splits into fields. *)
  Lemma split_fields : forall x : bits W,
    exists s E M, 0 <= M < 2 ^ f /\ 0 <= E < 2 ^ e /\
      Zmod.to_Z x = b2z s * 2 ^ (f + e) + E * 2 ^ f + M.
  Proof.
    intros x; pose proof He'.
    pose proof (bits.unsigned_range x ltac:(lia)) as Hr.
    assert (HW : 2 ^ W = 2 * 2 ^ (f + e)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hfe : 2 ^ (f + e) = 2 ^ f * 2 ^ e) by (apply Z.pow_add_r; lia).
    exists (2 ^ (f + e) <=? Zmod.to_Z x).
    set (r := Zmod.to_Z x mod 2 ^ (f + e)).
    exists (r / 2 ^ f), (r mod 2 ^ f).
    assert (Hr1 : 0 <= r < 2 ^ (f + e)) by (apply Z.mod_pos_bound; lia).
    pose proof (Z.mod_pos_bound r (2 ^ f) ltac:(lia)).
    split; [lia |]; split.
    - split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; lia.
    - pose proof (Z.div_mod r (2 ^ f) ltac:(lia)).
      pose proof (Z.div_mod (Zmod.to_Z x) (2 ^ (f + e)) ltac:(lia)).
      destruct (Z.leb_spec (2 ^ (f + e)) (Zmod.to_Z x)); cbn [b2z].
      + assert (Zmod.to_Z x / 2 ^ (f + e) = 1) by (symmetry; apply Z.div_unique with (Zmod.to_Z x - 2 ^ (f + e)); lia).
        fold r in H2; lia.
      + assert (Zmod.to_Z x / 2 ^ (f + e) = 0) by (apply Z.div_small; lia).
        fold r in H2; lia.
  Qed.

  (* Decoding then encoding a non-NaN pattern gives it back. *)
  Lemma ofB_toB : forall x : bits W, BinarySingleNaN.is_nan (toB x) = false -> ofB (toB x) = x.
  Proof.
    intros x Hn; unfold Glue.ofB, Glue.toB in *.
    assert (E : BSN2B prec emax (canonNaN e f Hf) (B2BSN prec emax (toBp x)) = toBp x).
    { destruct (toBp x); try reflexivity; discriminate Hn. }
    rewrite E; unfold Glue.toBp.
    rewrite bits_of_binary_float_of_bits.
    - apply Zmod.of_Z_to_Z.
    - pose proof He'; pose proof (bits.unsigned_range x ltac:(lia)); lia.
  Qed.

  Lemma is_nan_B2SF : forall b : BinarySingleNaN.binary_float prec emax,
    BinarySingleNaN.is_nan b = match BinarySingleNaN.B2SF b with S754_nan => true | _ => false end.
  Proof. intros [| | |]; reflexivity. Qed.
End Decode.
