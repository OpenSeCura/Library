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
 * Lemmas about the architectural FP state (`FpuArchLemmas.v`):
 * - the register paths have length 32 and are pairwise distinct (`fprPaths_length`, `fprPaths_NoDup`);
 * - each action of `FpuArch.v` in terms of the Gallina views (`evalActionPropGen_arch*`);
 * - read-after-write algebra of the views (`archFpr_setFpr_same`, ...).
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Fpu Require Import FpuArch.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * 1. SHAPE OF THE REGISTER PATHS
 * =========================================================================== *)

Lemma NoDup_map_inj : forall {A B : Type} (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd.
  apply NoDup_map_NoDup_ForallPairs; [intros x y _ _; apply Hinj | exact Hnd].
Qed.

Lemma getTreeRegsOfKind_regLeaf : forall (name : string) (r : Reg) (k : Kind),
  regKind r = k ->
  exists rk, getTreeRegsOfKind k (Leaf name (EReg r)) = [rk] /\ rk.(rk_path).(regPath) = tt.
Proof.
  intros name r k Hk; subst k.
  cbn [getTreeRegsOfKind].
  pose (target_prop := Is_true (Kind_eqb (regKind r) (regKind r))).
  set (mk_pf := fun pf : Kind_eqb (regKind r) (regKind r) = true =>
    (eq_rect_r (fun b' : bool => Is_true b') (I : Is_true true) pf : target_prop)).
  change (eq_rect_r (fun b' : bool => Is_true b') (I : Is_true true)) with mk_pf.
  generalize (eq_refl (Kind_eqb (regKind r) (regKind r))).
  generalize mk_pf.
  rewrite (Kind_eqb_refl (regKind r)).
  intros mk_pf' pf.
  eexists; split; reflexivity.
Qed.

(* The register paths of a node whose children are all registers of kind `k`. *)
Definition regLeafOf (k : Kind) (t : Tree Elem) : Prop :=
  exists name init, t = Leaf name (EReg (Build_Reg k init)).

Lemma getTreeRegsOfKind_regNode_length : forall (k : Kind) (name : string) (ls : list (Tree Elem)),
  Forall (regLeafOf k) ls ->
  length (getTreeRegsOfKind k (Node name ls)) = length ls.
Proof.
  intros k name ls Hall.
  induction Hall as [| x xs Hx Hxs IH].
  - reflexivity.
  - destruct Hx as [nm [init ->]].
    destruct (getTreeRegsOfKind_regLeaf nm (Build_Reg k init) k eq_refl) as [rk [Hrk _]].
    change (length (map (fun p : RegOfKind (t := Leaf nm (EReg (Build_Reg k init))) k =>
                           {| rk_path := {| regPath := (inl p.(rk_path).(regPath) : LeafPath (Node name (Leaf nm (EReg (Build_Reg k init)) :: xs)));
                                            regPathPf := p.(rk_path).(regPathPf) |} ;
                              rk_pf := p.(rk_pf) |})
                        (getTreeRegsOfKind k (Leaf nm (EReg (Build_Reg k init)))) ++
                    map (fun p : RegOfKind (t := Node name xs) k =>
                           {| rk_path := {| regPath := (inr p.(rk_path).(regPath) : LeafPath (Node name (Leaf nm (EReg (Build_Reg k init)) :: xs)));
                                            regPathPf := p.(rk_path).(regPathPf) |} ;
                              rk_pf := p.(rk_pf) |})
                        (getTreeRegsOfKind k (Node name xs))) = S (length xs)).
    rewrite length_app, !length_map, Hrk, IH; reflexivity.
Qed.

Lemma getTreeRegsOfKind_regNode_NoDup : forall (k : Kind) (name : string) (ls : list (Tree Elem)),
  Forall (regLeafOf k) ls ->
  NoDup (map (fun r : RegOfKind (t := Node name ls) k => r.(rk_path).(regPath))
             (getTreeRegsOfKind k (Node name ls))).
Proof.
  intros k name ls Hall.
  induction Hall as [| x xs Hx Hxs IH].
  - constructor.
  - destruct Hx as [nm [init ->]].
    destruct (getTreeRegsOfKind_regLeaf nm (Build_Reg k init) k eq_refl) as [rk [Hrk Hpath]].
    change (NoDup (map (fun r : RegOfKind (t := Node name (Leaf nm (EReg (Build_Reg k init)) :: xs)) k => r.(rk_path).(regPath))
             (map (fun p : RegOfKind (t := Leaf nm (EReg (Build_Reg k init))) k =>
                     {| rk_path := {| regPath := (inl p.(rk_path).(regPath) : LeafPath (Node name (Leaf nm (EReg (Build_Reg k init)) :: xs)));
                                      regPathPf := p.(rk_path).(regPathPf) |} ;
                        rk_pf := p.(rk_pf) |})
                  (getTreeRegsOfKind k (Leaf nm (EReg (Build_Reg k init)))) ++
              map (fun p : RegOfKind (t := Node name xs) k =>
                     {| rk_path := {| regPath := (inr p.(rk_path).(regPath) : LeafPath (Node name (Leaf nm (EReg (Build_Reg k init)) :: xs)));
                                      regPathPf := p.(rk_path).(regPathPf) |} ;
                        rk_pf := p.(rk_pf) |})
                  (getTreeRegsOfKind k (Node name xs))))).
    rewrite Hrk, map_app, !map_map; cbn [map app].
    constructor.
    + rewrite in_map_iff; intros [p [Hp _]]; discriminate Hp.
    + apply (NoDup_map_inj (fun lp : LeafPath (Node name xs) => (inr lp : LeafPath (Node name (Leaf nm (EReg (Build_Reg k init)) :: xs))))) in IH;
        [| intros a b H; injection H; auto].
      rewrite map_map in IH; exact IH.
Qed.

Section ArchLemmas.
  Variable flen : Z.

  Lemma fprLeaves_regLeaf : Forall (regLeafOf (Bit flen)) (fprLeaves flen).
  Proof.
    unfold fprLeaves; apply Forall_map, Forall_forall; intros i _.
    eexists; eexists; reflexivity.
  Qed.

  Lemma fprPaths_length : length (fprPaths flen) = NumFprs.
  Proof.
    unfold fprPaths, fprsTree.
    rewrite getTreeRegsOfKind_regNode_length by apply fprLeaves_regLeaf.
    unfold fprLeaves; rewrite length_map, length_seq; reflexivity.
  Qed.

  Lemma fprPaths_NoDup :
    NoDup (map (fun r : RegOfKind (t := fprsTree flen) (Bit flen) => r.(rk_path).(regPath)) (fprPaths flen)).
  Proof. apply getTreeRegsOfKind_regNode_NoDup, fprLeaves_regLeaf. Qed.

  Lemma fprPaths_length_pow : Z.of_nat (length (fprPaths flen)) = 2 ^ FprIdxSz.
  Proof. rewrite fprPaths_length; reflexivity. Qed.

  (* --- Read-after-write algebra of the views --- *)

  Lemma archFpr_setFpr_same : forall (s : ArchSt flen) i v, archFpr flen (archSetFpr flen s i v) i = v.
  Proof.
    intros s i v; unfold archFpr, archSetFpr, mkArch; cbn [Fst].
    exact (evalReadRegsList_evalWriteRegsList_same (fprPaths flen) i v s.(Fst) eq_refl fprPaths_length_pow).
  Qed.

  (* The FP registers are unchanged by the CSR / FS setters. *)
  Lemma archFpr_setFrm : forall (s : ArchSt flen) v j, archFpr flen (archSetFrm flen s v) j = archFpr flen s j.
  Proof. reflexivity. Qed.
  Lemma archFpr_setFflags : forall (s : ArchSt flen) v j, archFpr flen (archSetFflags flen s v) j = archFpr flen s j.
  Proof. reflexivity. Qed.
  Lemma archFpr_setFs : forall (s : ArchSt flen) v j, archFpr flen (archSetFs flen s v) j = archFpr flen s j.
  Proof. reflexivity. Qed.

  Lemma archFpr_setFpr_other : forall (s : ArchSt flen) i j v, j <> i ->
    archFpr flen (archSetFpr flen s i v) j = archFpr flen s j.
  Proof.
    intros s i j v Hne; unfold archFpr, archSetFpr, mkArch; cbn [Fst].
    exact (evalReadRegsList_evalWriteRegsList_other (fprPaths flen) j i v s.(Fst) fprPaths_NoDup Hne).
  Qed.

  Lemma archSetFpr_comm : forall (s : ArchSt flen) i j vi vj, i <> j ->
    archSetFpr flen (archSetFpr flen s i vi) j vj = archSetFpr flen (archSetFpr flen s j vj) i vi.
  Proof.
    intros s i j vi vj Hne; unfold archSetFpr, mkArch; cbn [Fst Snd].
    rewrite (evalWriteRegsList_comm (fprPaths flen) i j vi vj) by (apply fprPaths_NoDup || exact Hne).
    reflexivity.
  Qed.

  (* --- Actions in terms of the views --- *)
  Context {env : Env (fpuArchTree flen)}.

  Lemma evalActionPropGen_archReadFpr : forall (idx : Expr type (Bit FprIdxSz)) (s : ArchSt flen) P,
    evalActionPropGen env (archReadFpr flen type idx) s P <-> P s (archFpr flen s (evalExpr idx)).
  Proof.
    intros idx [sf rest] P; unfold archReadFpr, fpuArchTree in *.
    rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_readRegsList; reflexivity.
  Qed.

  Lemma evalActionPropGen_archWriteFpr : forall (idx : Expr type (Bit FprIdxSz)) (v : Expr type (Bit flen)) (s : ArchSt flen) P,
    evalActionPropGen env (archWriteFpr flen type idx v) s P <->
    P (archSetFpr flen s (evalExpr idx) (evalExpr v)) Zmod.zero.
  Proof.
    intros idx v [sf [frm [ff [fs []]]]] P; unfold archWriteFpr, fpuArchTree in *.
    rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_writeRegsList; reflexivity.
  Qed.

  Lemma evalActionPropGen_archReadFrm : forall (s : ArchSt flen) P,
    evalActionPropGen env (archReadFrm flen type) s P <-> P s (archFrm flen s).
  Proof. intros [sf [frm [ff [fs []]]]] P; reflexivity. Qed.

  Lemma evalActionPropGen_archWriteFrm : forall (v : Expr type (Bit 3)) (s : ArchSt flen) P,
    evalActionPropGen env (archWriteFrm flen type v) s P <-> P (archSetFrm flen s (evalExpr v)) Zmod.zero.
  Proof. intros v [sf [frm [ff [fs []]]]] P; reflexivity. Qed.

  Lemma evalActionPropGen_archReadFflags : forall (s : ArchSt flen) P,
    evalActionPropGen env (archReadFflags flen type) s P <-> P s (archFflags flen s).
  Proof. intros [sf [frm [ff [fs []]]]] P; reflexivity. Qed.

  Lemma evalActionPropGen_archWriteFflags : forall (v : Expr type (Bit 5)) (s : ArchSt flen) P,
    evalActionPropGen env (archWriteFflags flen type v) s P <-> P (archSetFflags flen s (evalExpr v)) Zmod.zero.
  Proof. intros v [sf [frm [ff [fs []]]]] P; reflexivity. Qed.

  Lemma evalActionPropGen_archReadFs : forall (s : ArchSt flen) P,
    evalActionPropGen env (archReadFs flen type) s P <-> P s (archFs flen s).
  Proof. intros [sf [frm [ff [fs []]]]] P; reflexivity. Qed.

  Lemma evalActionPropGen_archWriteFs : forall (v : Expr type (Bit 2)) (s : ArchSt flen) P,
    evalActionPropGen env (archWriteFs flen type v) s P <-> P (archSetFs flen s (evalExpr v)) Zmod.zero.
  Proof. intros v [sf [frm [ff [fs []]]]] P; reflexivity. Qed.
End ArchLemmas.
