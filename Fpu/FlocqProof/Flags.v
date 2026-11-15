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
 * IEEE 754 exception flags, specified from Flocq's real values (`Flags.v`).
 *
 * Flocq does not model the IEEE status flags; this is the small flag spec used by the per-op
 * theorems.  For an operation whose exact result is the real `p` (finite operands):
 * - overflow  (OF): the result rounded with unbounded exponent range is at least 2^emax in
 *   magnitude (Flocq's overflow condition in `Bmult_correct` etc.);
 * - inexact   (NX): overflow, or the correctly rounded result differs from `p`;
 * - underflow (UF): tiny AFTER rounding (RISC-V / IEEE 754-2008 option): the value rounded to the
 *   precision with unbounded exponent range is below the minimum normal 2^(2 - emax) in
 *   magnitude, and the result is inexact;
 * - invalid (NV) and divide-by-zero (DZ) are given per operation.
 * The 5-bit encoding is RISC-V `fflags` = {NV, DZ, OF, UF, NX}.
 *)

From Stdlib Require Import ZArith Zmod Reals Lia.
From Flocq Require Import Core.Zaux Core.Raux Core.Generic_fmt Core.FLX IEEE754.BinarySingleNaN.
From Guru Require Import Primitives.

Local Open Scope Z_scope.

Definition b2z (b : bool) : Z := if b then 1 else 0.

(* RISC-V `fflags` from the five flags. *)
Definition mkFl (nv dz ovf uf nx : bool) : bits 5 :=
  Zmod.of_Z _ (16 * b2z nv + 8 * b2z dz + 4 * b2z ovf + 2 * b2z uf + b2z nx).

Section Flags.
  Variable prec emax : Z.

  (* Flags of rounding the exact finite result `p` with mode `m`. *)
  Definition roundFlags (m : mode) (p : R) : bool * bool * bool :=
    let r := round radix2 (SpecFloat.fexp prec emax) (round_mode m) p in
    let ovf := negb (Rlt_bool (Rabs r) (bpow radix2 emax)) in
    let nx := (ovf || negb (Req_bool r p))%bool in
    let tiny := Rlt_bool (Rabs (round radix2 (FLX_exp prec) (round_mode m) p)) (bpow radix2 (2 - emax)) in
    (ovf, (tiny && nx && negb ovf)%bool, nx).

  Definition finiteFlags (m : mode) (p : R) : bits 5 :=
    let '(ovf, uf, nx) := roundFlags m p in mkFl false false ovf uf nx.
End Flags.
