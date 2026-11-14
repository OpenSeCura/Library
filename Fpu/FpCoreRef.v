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
 * The readable reference model of the floating-point core (`FpCoreRef.v`).
 *
 * Internal exponents are UNBIASED: the bias is removed when an operand is unpacked and added back
 * when the result is packed.  The model shares every definition with the hardware model of
 * `FpCore.v`; the two differ only in the exponent mode `bm` (`expOff` = bias or 0, and
 * `expUnpack`), so the significand datapath is literally the same code.
 *
 * `Proof/FpCoreRefProof.v` proves that both models compute the same results for every format
 * satisfying `2 <= e`, `2 <= f`, `4 f + 5 <= 6 * 2^(e-1)` (and, for the integer conversions,
 * `0 <= xlen`, `xlen + 4 <= 7 * 2^(e-1)`): `fpuComputeRef_equiv`, `cvtFFRef_equiv`.
 *)

From Stdlib Require Import ZArith.
From Guru Require Import Primitives Syntax.
From Fpu Require Import FpCore.

Definition fpuComputeRef := fpuCompute false.

Definition cvtFFRef := cvtFF false.
