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
 * Lemmas about the atomic FPU spec (`SpecFpuLemmas.v`):
 * - every action of `SpecFpu.v` computes its Gallina semantics (`evalActionPropGen_fpuExec`, ...);
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Fpu Require Import FpUtil FpCore FpuArch SpecFpu FpuArchLemmas.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* OR on bit vectors. *)
Lemma bits_or_0_l : forall n (x : bits n), Zmod.or Zmod.zero x = x.
Proof. intros n x; apply Zmod.to_Z_inj; rewrite bits.unsigned_or, Zmod.to_Z_0; apply Z.lor_0_l. Qed.

Lemma bits_or_0_r : forall n (x : bits n), Zmod.or x Zmod.zero = x.
Proof. intros n x; apply Zmod.to_Z_inj; rewrite bits.unsigned_or, Zmod.to_Z_0; apply Z.lor_0_r. Qed.

Lemma bits_or_comm : forall n (x y : bits n), Zmod.or x y = Zmod.or y x.
Proof. intros n x y; apply Zmod.to_Z_inj; rewrite !bits.unsigned_or; apply Z.lor_comm. Qed.

Lemma bits_or_assoc : forall n (x y z : bits n), Zmod.or (Zmod.or x y) z = Zmod.or x (Zmod.or y z).
Proof. intros n x y z; apply Zmod.to_Z_inj; rewrite !bits.unsigned_or; symmetry; apply Z.lor_assoc. Qed.

Lemma evalExpr_Or2 : forall w (a b : Expr type (Bit w)),
  evalExpr (Or [a; b]) = Zmod.or (evalExpr a) (evalExpr b).
Proof. intros w a b; cbn [evalExpr fold_left map]; apply (f_equal2 Zmod.or); [apply bits_or_0_l | reflexivity]. Qed.

(* One-step evaluation of action constructors (head position only). *)
Lemma evp_LetAction : forall {t} (env : Env t) s {k k'} (a : Action type t k') (cont : type k' -> Action type t k) S Q,
  evalActionPropGen env (LetAction s a cont) S Q <-> evalActionPropGen env a S (fun S' r => evalActionPropGen env (cont r) S' Q).
Proof. intros; apply iff_refl. Qed.

Lemma evp_LetExp : forall {t} (env : Env t) s {k k'} (e : Expr type k') (cont : type k' -> Action type t k) S Q,
  evalActionPropGen env (LetExp s e cont) S Q <-> evalActionPropGen env (cont (evalExpr e)) S Q.
Proof. intros; apply iff_refl. Qed.

Lemma evp_IfElse : forall {t} (env : Env t) s (p : Expr type Bool) {k k'} (tb fb : Action type t k')
  (cont : type k' -> Action type t k) S Q,
  evalActionPropGen env (IfElse s p tb fb cont) S Q <->
  (if evalExpr p then evalActionPropGen env tb S (fun S' r => evalActionPropGen env (cont r) S' Q)
   else evalActionPropGen env fb S (fun S' r => evalActionPropGen env (cont r) S' Q)).
Proof. intros; cbn [evalActionPropGen]; destruct (evalExpr p); apply iff_refl. Qed.

Lemma evp_Return : forall {t} (env : Env t) {k} (e : Expr type k) S Q,
  evalActionPropGen env (Return e) S Q <-> Q S (evalExpr e).
Proof. intros; apply iff_refl. Qed.

Section SpecLemmas.
  Variable F : FpFmt.
  Variable xlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.
  Variable bm : bool.

  (* ---------------------------------------------------------------------------
   * 2. THE ACTIONS COMPUTE THEIR SEMANTICS
   * --------------------------------------------------------------------------- *)

  Context {env : Env (fpuArchTree flen)}.

  Lemma evalActionPropGen_fpuRead : forall (idx : Expr type (Bit FprIdxSz)) (s : ArchSt flen) P,
    evalActionPropGen env (fpuRead F type idx) s P <-> P s (archFpr flen s (evalExpr idx)).
  Proof. intros; apply evalActionPropGen_archReadFpr. Qed.

  Lemma evalActionPropGen_fpuWrite : forall (idx : Expr type (Bit FprIdxSz)) (v : Expr type (Bit flen)) (s : ArchSt flen) P,
    evalActionPropGen env (fpuWrite F type idx v) s P <->
    P (writeSem F s (evalExpr idx) (evalExpr v)) Zmod.zero.
  Proof.
    intros; unfold fpuWrite; cbn [evalActionPropGen].
    rewrite evalActionPropGen_archWriteFpr, evalActionPropGen_archWriteFs; reflexivity.
  Qed.

  Lemma evalActionPropGen_frmRead : forall (s : ArchSt flen) P,
    evalActionPropGen env (frmRead F type) s P <-> P s (archFrm flen s).
  Proof. intros; apply evalActionPropGen_archReadFrm. Qed.

  Lemma evalActionPropGen_frmWrite : forall (v : Expr type (Bit 3)) (s : ArchSt flen) P,
    evalActionPropGen env (frmWrite F type v) s P <-> P (frmWriteSem F s (evalExpr v)) Zmod.zero.
  Proof.
    intros; unfold frmWrite; cbn [evalActionPropGen].
    rewrite evalActionPropGen_archWriteFrm, evalActionPropGen_archWriteFs; reflexivity.
  Qed.

  Lemma evalActionPropGen_fflagsRead : forall (s : ArchSt flen) P,
    evalActionPropGen env (fflagsRead F type) s P <-> P s (archFflags flen s).
  Proof. intros; apply evalActionPropGen_archReadFflags. Qed.

  Lemma evalActionPropGen_fflagsWrite : forall (v : Expr type (Bit 5)) (s : ArchSt flen) P,
    evalActionPropGen env (fflagsWrite F type v) s P <-> P (fflagsWriteSem F s (evalExpr v)) Zmod.zero.
  Proof.
    intros; unfold fflagsWrite; cbn [evalActionPropGen].
    rewrite evalActionPropGen_archWriteFflags, evalActionPropGen_archWriteFs; reflexivity.
  Qed.

  Lemma evalActionPropGen_fcsrRead : forall (s : ArchSt flen) P,
    evalActionPropGen env (fcsrRead F type) s P <-> P s (fcsrOf F s).
  Proof.
    intros; unfold fcsrRead; cbn [evalActionPropGen].
    rewrite evalActionPropGen_archReadFrm, evalActionPropGen_archReadFflags; reflexivity.
  Qed.

  Lemma evalActionPropGen_fcsrWrite : forall (v : Expr type (Bit 8)) (s : ArchSt flen) P,
    evalActionPropGen env (fcsrWrite F type v) s P <-> P (fcsrWriteSem F s (evalExpr v)) Zmod.zero.
  Proof.
    intros; unfold fcsrWrite; cbn [evalActionPropGen].
    rewrite evalActionPropGen_archWriteFrm, evalActionPropGen_archWriteFflags, evalActionPropGen_archWriteFs.
    reflexivity.
  Qed.

  Lemma evalActionPropGen_fsRead : forall (s : ArchSt flen) P,
    evalActionPropGen env (fsRead F type) s P <-> P s (archFs flen s).
  Proof. intros; apply evalActionPropGen_archReadFs. Qed.

  Lemma evalActionPropGen_fsWrite : forall (v : Expr type (Bit 2)) (s : ArchSt flen) P,
    evalActionPropGen env (fsWrite F type v) s P <-> P (fsWriteSem F s (evalExpr v)) Zmod.zero.
  Proof. intros; apply evalActionPropGen_archWriteFs. Qed.

  Lemma evalActionPropGen_fpuExec : forall (pkt : type (FpuPktK narrow)) (x : bits xlen) (s : ArchSt flen) P,
    evalActionPropGen env (fpuExec bm F xlen narrow type pkt x) s P <->
    P (execSem bm F xlen narrow s pkt x) ((execRes bm F xlen narrow s pkt x) @% "xres").
  Proof.
    (* Head-position rewrites only: `cbn` here makes the kernel re-check expensive. *)
    intros pkt x s P; unfold fpuExec.
    rewrite evp_LetAction, evalActionPropGen_archReadFpr; cbv beta.
    rewrite evp_LetAction, evalActionPropGen_archReadFpr; cbv beta.
    rewrite evp_LetAction, evalActionPropGen_archReadFpr; cbv beta.
    rewrite evp_LetAction, evalActionPropGen_archReadFrm; cbv beta.
    rewrite evp_LetExp; cbv beta.
    rewrite evp_LetAction, evalActionPropGen_toAction; cbv beta.
    unfold execSem, execRes, applyRes.
    match goal with
    | |- context [evalLetExpr (execCompute ?bmv ?fF ?xl ?fn type pkt ?rm ?a ?b ?c x)] =>
        replace (evalLetExpr (execCompute bmv fF xl fn type pkt rm a b c x)) with
          (execResOf bm F xlen narrow pkt (rmOf pkt (archFrm flen s)) (archFpr flen s (pktRs1 pkt))
                     (archFpr flen s (pktRs2 pkt)) (archFpr flen s (pktRs3 pkt)) x)
          by (unfold execResOf; f_equal)
    end.
    set (r := execResOf bm F xlen narrow pkt _ _ _ _ x).
    rewrite evp_IfElse.
    change (evalExpr (##r`"writesF")) with (r @% "writesF").
    clearbody r.
    destruct (r @% "writesF") eqn:Hw.
    - rewrite evalActionPropGen_archWriteFpr; cbv beta.
      rewrite evp_LetAction, evalActionPropGen_archReadFflags; cbv beta.
      rewrite evp_LetAction, evalActionPropGen_archWriteFflags; cbv beta.
      rewrite evp_LetAction, evalActionPropGen_archWriteFs; cbv beta.
      rewrite evp_Return, evalExpr_Or2; cbn [evalExpr]; apply iff_refl.
    - rewrite evp_Return; cbv beta.
      rewrite evp_LetAction, evalActionPropGen_archReadFflags; cbv beta.
      rewrite evp_LetAction, evalActionPropGen_archWriteFflags; cbv beta.
      rewrite evp_LetAction, evalActionPropGen_archWriteFs; cbv beta.
      rewrite evp_Return, evalExpr_Or2; cbn [evalExpr]; apply iff_refl.
  Qed.
End SpecLemmas.

(* ---------------------------------------------------------------------------
 * 3. THE OPERATION UNION: DECODING A BUILT OPERATION
 *
 * For a parent's decoder: decoding the union built for a family gives that family's flag and
 * options (all other flags false, other options cleared).
 * --------------------------------------------------------------------------- *)

Section OpUnion.
  Variable narrow : list FpFmt.

  Local Abbreviation OpL := (FpuOpList narrow).
  Local Abbreviation OpK := (FpuOpK narrow).

  Lemma kindWf_CvtNOptK : kindWf (CvtNOptK narrow) = true.
  Proof.
    unfold CvtNOptK, NIdxSz; cbn [kindWf snd andb].
    rewrite (proj2 (Z.leb_le _ _) (Z.log2_up_nonneg _)); reflexivity.
  Qed.

  Definition decOf (op : type OpK) : type FpOpDK := evalLetExpr (decodeOp narrow type op).

  (* Field projections of the decoded record (stated once; cheap lemma statements). *)
  Definition d_add (d : type FpOpDK) : bool := d @% "add".
  Definition d_mul (d : type FpOpDK) : bool := d @% "mul".
  Definition d_fma (d : type FpOpDK) : bool := d @% "fma".
  Definition d_div (d : type FpOpDK) : bool := d @% "div".
  Definition d_sqrt (d : type FpOpDK) : bool := d @% "sqrt".
  Definition d_minmax (d : type FpOpDK) : bool := d @% "minmax".
  Definition d_sgnj (d : type FpOpDK) : bool := d @% "sgnj".
  Definition d_cmp (d : type FpOpDK) : bool := d @% "cmp".
  Definition d_fclass (d : type FpOpDK) : bool := d @% "fclass".
  Definition d_cvtFI (d : type FpOpDK) : bool := d @% "cvtFI".
  Definition d_cvtIF (d : type FpOpDK) : bool := d @% "cvtIF".
  Definition d_round (d : type FpOpDK) : bool := d @% "round".
  Definition d_negB (d : type FpOpDK) : bool := d @% "negB".
  Definition d_negProd (d : type FpOpDK) : bool := d @% "negProd".
  Definition d_negAdd (d : type FpOpDK) : bool := d @% "negAdd".
  Definition d_isMax (d : type FpOpDK) : bool := d @% "isMax".
  Definition d_nanProp (d : type FpOpDK) : bool := d @% "nanProp".
  Definition d_mode (d : type FpOpDK) : bits 2 := d @% "mode".
  Definition d_quiet (d : type FpOpDK) : bool := d @% "quiet".
  Definition d_unsigned (d : type FpOpDK) : bool := d @% "unsigned".
  Definition d_wide (d : type FpOpDK) : bool := d @% "wide".
  Definition d_nx (d : type FpOpDK) : bool := d @% "nx".

  (* The union built for the family at position `k` of `FpuOpList` (0 = add, ..., 12 = cvtN). *)
  Local Abbreviation mkOp k p := (@BuildUnion type OpL (@Build_FinType (length OpL) k%nat I) p).

  (* An option of the built family reads back with Guru's round-trip lemma, applied to the read
   * term taken from the goal (`constr_eq`: the built family's own read). *)
  Ltac opt_tac :=
    intros; unfold d_add, d_mul, d_fma, d_div, d_sqrt, d_minmax, d_sgnj, d_cmp, d_fclass, d_cvtFI,
      d_cvtIF, d_round, d_negB, d_negProd, d_negAdd, d_isMax, d_nanProp, d_mode, d_quiet, d_unsigned,
      d_wide, d_nx, decOf, decodeOp; cbn [evalLetExpr];
    match goal with |- context [?x] =>
      match x with evalExpr (ReadUnionData (Var _ _ (evalExpr (BuildUnion ?i ?e))) ?j) =>
        let a := eval cbv in (finNum i) in let b := eval cbv in (finNum j) in constr_eq a b;
        let Hr := fresh in
        assert (Hr : x = evalExpr e) by exact (evalExpr_ReadUnionData_BuildUnion OpL i e eq_refl);
        rewrite Hr; clear Hr
      end
    end;
    exact eq_refl.

  Lemma decode_add : forall p : Expr type AddOptK, d_add (decOf (evalExpr (mkOp 0 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_add_negB : forall p : Expr type AddOptK,
    d_negB (decOf (evalExpr (mkOp 0 p))) = (evalExpr p) @% "negB".
  Proof. opt_tac. Qed.

  Lemma decode_mul : d_mul (decOf (evalExpr (mkOp 1 (Const type (Bit 0) Zmod.zero)))) = true.
  Proof. exact eq_refl. Qed.

  Lemma decode_fma : forall p : Expr type FmaOptK, d_fma (decOf (evalExpr (mkOp 2 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_fma_negProd : forall p : Expr type FmaOptK,
    d_negProd (decOf (evalExpr (mkOp 2 p))) = (evalExpr p) @% "negProd".
  Proof. opt_tac. Qed.

  Lemma decode_fma_negAdd : forall p : Expr type FmaOptK,
    d_negAdd (decOf (evalExpr (mkOp 2 p))) = (evalExpr p) @% "negAdd".
  Proof. opt_tac. Qed.

  Lemma decode_div : d_div (decOf (evalExpr (mkOp 3 (Const type (Bit 0) Zmod.zero)))) = true.
  Proof. exact eq_refl. Qed.

  Lemma decode_sqrt : d_sqrt (decOf (evalExpr (mkOp 4 (Const type (Bit 0) Zmod.zero)))) = true.
  Proof. exact eq_refl. Qed.

  Lemma decode_minmax : forall p : Expr type MinMaxOptK, d_minmax (decOf (evalExpr (mkOp 5 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_minmax_isMax : forall p : Expr type MinMaxOptK,
    d_isMax (decOf (evalExpr (mkOp 5 p))) = (evalExpr p) @% "isMax".
  Proof. opt_tac. Qed.

  Lemma decode_minmax_nanProp : forall p : Expr type MinMaxOptK,
    d_nanProp (decOf (evalExpr (mkOp 5 p))) = (evalExpr p) @% "nanProp".
  Proof. opt_tac. Qed.

  Lemma decode_sgnj : forall p : Expr type SgnjOptK, d_sgnj (decOf (evalExpr (mkOp 6 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_sgnj_mode : forall p : Expr type SgnjOptK,
    d_mode (decOf (evalExpr (mkOp 6 p))) = (evalExpr p) @% "mode".
  Proof. opt_tac. Qed.

  Lemma decode_cmp : forall p : Expr type CmpOptK, d_cmp (decOf (evalExpr (mkOp 7 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_cmp_mode : forall p : Expr type CmpOptK,
    d_mode (decOf (evalExpr (mkOp 7 p))) = (evalExpr p) @% "mode".
  Proof. opt_tac. Qed.

  Lemma decode_cmp_quiet : forall p : Expr type CmpOptK,
    d_quiet (decOf (evalExpr (mkOp 7 p))) = (evalExpr p) @% "quiet".
  Proof. opt_tac. Qed.

  Lemma decode_fclass : d_fclass (decOf (evalExpr (mkOp 8 (Const type (Bit 0) Zmod.zero)))) = true.
  Proof. exact eq_refl. Qed.

  Lemma decode_cvtFI : forall p : Expr type CvtOptK, d_cvtFI (decOf (evalExpr (mkOp 9 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_cvtFI_unsigned : forall p : Expr type CvtOptK,
    d_unsigned (decOf (evalExpr (mkOp 9 p))) = (evalExpr p) @% "unsigned".
  Proof. opt_tac. Qed.

  Lemma decode_cvtFI_wide : forall p : Expr type CvtOptK,
    d_wide (decOf (evalExpr (mkOp 9 p))) = (evalExpr p) @% "wide".
  Proof. opt_tac. Qed.

  Lemma decode_cvtIF : forall p : Expr type CvtOptK, d_cvtIF (decOf (evalExpr (mkOp 10 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_cvtIF_unsigned : forall p : Expr type CvtOptK,
    d_unsigned (decOf (evalExpr (mkOp 10 p))) = (evalExpr p) @% "unsigned".
  Proof. opt_tac. Qed.

  Lemma decode_cvtIF_wide : forall p : Expr type CvtOptK,
    d_wide (decOf (evalExpr (mkOp 10 p))) = (evalExpr p) @% "wide".
  Proof. opt_tac. Qed.

  Lemma decode_round : forall p : Expr type RoundOptK, d_round (decOf (evalExpr (mkOp 11 p))) = true.
  Proof. intros; exact eq_refl. Qed.

  Lemma decode_round_nx : forall p : Expr type RoundOptK,
    d_nx (decOf (evalExpr (mkOp 11 p))) = (evalExpr p) @% "nx".
  Proof. opt_tac. Qed.

  (* A narrow conversion is no core family; its options read back from the union. *)
  Lemma decode_cvtN_add : forall p : Expr type (CvtNOptK narrow),
    d_add (decOf (evalExpr (mkOp 12 p))) = false.
  Proof. intros; exact eq_refl. Qed.

  Lemma cvtN_payload : forall p : Expr type (CvtNOptK narrow),
    evalExpr ((Var type OpK (evalExpr (mkOp 12 p))) `! "cvtN") = evalExpr p.
  Proof.
    intros p; match goal with |- evalExpr (ReadUnionData (Var _ _ (evalExpr (BuildUnion ?i ?e))) _) = _ =>
      exact (evalExpr_ReadUnionData_BuildUnion OpL i e kindWf_CvtNOptK) end.
  Qed.

  Lemma isNarrow_cvtN : forall p : Expr type (CvtNOptK narrow),
    evalExpr (isNarrowE narrow type (evalExpr (mkOp 12 p))) = true.
  Proof. intros; reflexivity. Qed.
End OpUnion.
