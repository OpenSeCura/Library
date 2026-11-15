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
 * Glue between the Fpu bit-vectors and Flocq's IEEE 754 binary floats (`Glue.v`).
 *
 * A format `(e, f)` (exponent bits, fraction bits) is Flocq's `binary_float prec emax` with
 * `prec = f + 1` and `emax = 2^(e-1)`.  Encoding and decoding use Flocq's own `IEEE754.Bits`
 * (`binary_float_of_bits` / `bits_of_binary_float`), so the bit layout is Flocq's, not ours.
 * We target `BinarySingleNaN` (one NaN): decoding forgets the payload, encoding produces the
 * RISC-V canonical NaN (sign 0, quiet bit set, rest 0).
 *
 * Formats need `2 <= f` and Flocq's `f + 1 < 2^(e-1)` (the same condition as Fpu's `FmtOk`).
 *
 * `modeOf` maps the RISC-V rounding-mode field to Flocq's modes; like `FpCore`, the values 5..7
 * behave as RNE (the spec resolves DYN = 7 before the core is called).
 *)

From Stdlib Require Import ZArith Zmod Lia.
From Stdlib Require Import Floats.SpecFloat.
From Flocq Require Import Core.Zaux Core.Digits IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Guru Require Import Primitives.

Local Open Scope Z_scope.

Section Glue.
  Variable e f : Z.
  Hypothesis Hf : 2 <= f.
  (* Flocq's own requirement (`Prec_lt_emax`): the precision is below emax.  Not implied by the
   * Fpu condition `FmtOk`; all standard formats satisfy both (binary16: 11 < 16). *)
  Hypothesis Hpe : f + 1 < 2 ^ (e - 1).

  Local Abbreviation prec := (f + 1).
  Local Abbreviation emax := (2 ^ (e - 1)).
  Local Abbreviation W := (f + e + 1).

  (* The format condition implies `2 <= e`. *)
  Lemma He : 2 <= e.
  Proof.
    destruct (Z_lt_le_dec (e - 1) 0) as [Hn | Hn]; [rewrite Z.pow_neg_r in Hpe by lia; lia |].
    destruct (Z_lt_le_dec (e - 1) 1) as [H1 | H1]; [replace (e - 1) with 0 in Hpe by lia; cbn in Hpe; lia | lia].
  Qed.

  (* Side conditions of Flocq's encoding and arithmetic. *)
  Lemma Hmw : 0 < f.
  Proof. lia. Qed.

  Lemma Hew : 0 < e.
  Proof. pose proof He; lia. Qed.

  Lemma Hmax : f + 1 < 2 ^ (e - 1).
  Proof. lia. Qed.

  Lemma prec_gt_0 : FLX.Prec_gt_0 prec.
  Proof. unfold FLX.Prec_gt_0; lia. Qed.

  Lemma prec_lt_emax : Prec_lt_emax prec emax.
  Proof. unfold Prec_lt_emax; lia. Qed.

  (* ---------------------------------------------------------------------------
   * Decoding and encoding
   * --------------------------------------------------------------------------- *)

  (* Flocq's float with payloads, decoded from our bits. *)
  Definition toBp (x : bits W) : Binary.binary_float prec emax :=
    binary_float_of_bits f e Hmw Hew Hmax (Zmod.to_Z x).

  Definition toB (x : bits W) : BinarySingleNaN.binary_float prec emax := B2BSN prec emax (toBp x).

  (* The RISC-V canonical NaN: payload 2^(f-1) (the quiet bit), sign 0. *)
  Lemma canon_pl : nan_pl prec (Z.to_pos (2 ^ (f - 1))) = true.
  Proof.
    unfold nan_pl; apply Z.ltb_lt.
    rewrite Zpos_digits2_pos, Z2Pos.id by (apply Z.pow_pos_nonneg; lia).
    rewrite Zdigits_Zpower by lia; lia.
  Qed.

  Definition canonNaN : {x : Binary.binary_float prec emax | Binary.is_nan prec emax x = true} :=
    exist _ (@Binary.B754_nan prec emax false (Z.to_pos (2 ^ (f - 1))) canon_pl) eq_refl.

  Definition ofB (b : BinarySingleNaN.binary_float prec emax) : bits W :=
    Zmod.of_Z _ (bits_of_binary_float f e (BSN2B prec emax canonNaN b)).

  (* Rounding mode: RNE 0, RTZ 1, RDN 2, RUP 3, RMM 4; anything else behaves as RNE. *)
  Definition modeOf (rm : bits 3) : mode :=
    match Zmod.to_Z rm with
    | 1 => mode_ZR
    | 2 => mode_DN
    | 3 => mode_UP
    | 4 => mode_NA
    | _ => mode_NE
    end.

  (* Our decoding is Flocq's: decoding the encoding of a float gives it back. *)
  Lemma toB_ofB : forall b, toB (ofB b) = b.
  Proof.
    intros b; unfold toB, toBp, ofB.
    rewrite Zmod.unsigned_of_Z, Z.mod_small.
    - rewrite binary_float_of_bits_of_binary_float; apply B2BSN_BSN2B.
    - pose proof He; apply bits_of_binary_float_range; lia.
  Qed.
End Glue.
