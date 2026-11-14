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
 * Architectural FP state (`FpuArch.v`), shared by the spec and the impl.
 *
 * `fpuArchTree flen` = Node "" [ fprs ; frm ; fflags ; fs ] where `fprs` is the list of 32
 * `flen`-bit registers `fpr_0 .. fpr_1f` (accessed with Guru's `readRegsList` / `writeRegsList`),
 * `frm` (3 bits), `fflags` (5 bits) and `fs` (the 2-bit `mstatus.FS` field).
 *
 * Gallina views of a state (`archFpr`, `archFrm`, `archFflags`, `archFs`) and updates
 * (`archSetFpr`, ...) are used by the proofs; `Proof/FpuArchLemmas.v` relates the actions below
 * to them.
 *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Guru Require Import Primitives Library Syntax Combinators Notations Composition Semantics HelperLemmas.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Definition FprIdxSz : Z := 5.
Definition NumFprs : nat := 32.

Section FpuArch.
  Variable flen : Z.

  Definition fprLeaves : list (Tree Elem) :=
    map (fun i => Leaf ("fpr_" ++ hex_string_of_Z (Z.of_nat i))
                       (EReg (Build_Reg (Bit flen) (Some (getDefault _)))))
        (seq 0 NumFprs).

  Definition fprsTree : Tree Elem := Node "fprs" fprLeaves.

  Definition fprPaths : list (RegOfKind (t:=fprsTree) (Bit flen)) :=
    getTreeRegsOfKind (Bit flen) fprsTree.

  Definition fpuArchTree : Tree Elem :=
    Node "" [
      fprsTree ;
      Leaf "frm"    (EReg (Build_Reg (Bit 3) (Some (getDefault _)))) ;
      Leaf "fflags" (EReg (Build_Reg (Bit 5) (Some (getDefault _)))) ;
      Leaf "fs"     (EReg (Build_Reg (Bit 2) (Some (getDefault _))))
    ].

  (* --- Actions --- *)
  Section Actions.
    Variable ty : Kind -> Type.

    Definition archReadFpr (idx : Expr ty (Bit FprIdxSz)) : Action ty fpuArchTree (Bit flen) :=
      liftAction child0Path (readRegsList fprPaths idx).

    Definition archWriteFpr (idx : Expr ty (Bit FprIdxSz)) (v : Expr ty (Bit flen)) : Action ty fpuArchTree (Bit 0) :=
      liftAction child0Path (writeRegsList fprPaths idx v).

    Definition archReadFrm : Action ty fpuArchTree (Bit 3) :=
      RegRead v <- ".frm" in fpuArchTree ; Return (#v).

    Definition archWriteFrm (v : Expr ty (Bit 3)) : Action ty fpuArchTree (Bit 0) :=
      RegWrite ".frm" in fpuArchTree <- v ; Retv.

    Definition archReadFflags : Action ty fpuArchTree (Bit 5) :=
      RegRead v <- ".fflags" in fpuArchTree ; Return (#v).

    Definition archWriteFflags (v : Expr ty (Bit 5)) : Action ty fpuArchTree (Bit 0) :=
      RegWrite ".fflags" in fpuArchTree <- v ; Retv.

    Definition archReadFs : Action ty fpuArchTree (Bit 2) :=
      RegRead v <- ".fs" in fpuArchTree ; Return (#v).

    Definition archWriteFs (v : Expr ty (Bit 2)) : Action ty fpuArchTree (Bit 0) :=
      RegWrite ".fs" in fpuArchTree <- v ; Retv.
  End Actions.

  (* --- Gallina views and updates --- *)
  Definition ArchSt : Type := TreeState ElemState fpuArchTree.

  Definition archFpr (s : ArchSt) (i : bits FprIdxSz) : bits flen :=
    evalReadRegsList fprPaths i s.(Fst).
  Definition archFrm (s : ArchSt) : bits 3 := s.(Snd).(Fst).
  Definition archFflags (s : ArchSt) : bits 5 := s.(Snd).(Snd).(Fst).
  Definition archFs (s : ArchSt) : bits 2 := s.(Snd).(Snd).(Snd).(Fst).

  Definition mkArch (fprs : TreeState ElemState fprsTree) (frm : bits 3) (ff : bits 5) (fs : bits 2) : ArchSt :=
    (fprs ,, (frm ,, (ff ,, (fs ,, tt)))).

  Definition archSetFpr (s : ArchSt) (i : bits FprIdxSz) (v : bits flen) : ArchSt :=
    mkArch (evalWriteRegsList fprPaths i v s.(Fst)) (archFrm s) (archFflags s) (archFs s).
  Definition archSetFrm (s : ArchSt) (v : bits 3) : ArchSt :=
    mkArch s.(Fst) v (archFflags s) (archFs s).
  Definition archSetFflags (s : ArchSt) (v : bits 5) : ArchSt :=
    mkArch s.(Fst) (archFrm s) v (archFs s).
  Definition archSetFs (s : ArchSt) (v : bits 2) : ArchSt :=
    mkArch s.(Fst) (archFrm s) (archFflags s) v.
End FpuArch.
