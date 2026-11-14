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
 * FU correctness (`FpuFUProof.v`).
 *
 * `FUOk L V`: fu `L`, viewed through `V` (`lvHolds s xs`: state `s` holds the inputs `xs`,
 * oldest first), is a FIFO whose head, when `fuFirst` says valid, is `fuSpec x` -- the
 * destination and the spec result `SpecFpu.execResOf` of the input.  All obligations are forward
 * lemmas over `evalActionPropGen`, for every environment.
 *
 * Instances: `pipeFU_ok`, `divFU_ok`, `sqrtFU_ok`, `cvtFU_ok`, and `fpuFUs_ok` for the
 * standard fu list.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Fpu Require Import FpUtil FpCore IntMul ImplStaged ImplFpuUnits FpuArch SpecFpu FpuFU.
From Fpu Require Import FpUtilLemmas FpuUnitsProof SpecFpuLemmas StagedQueue.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Open Scope list_scope.

Lemma fold_left_andb_true : forall (l : list bool) b,
  fold_left andb l b = true -> b = true /\ Forall (fun x => x = true) l.
Proof.
  induction l as [| y l IH]; intros b H; cbn [fold_left] in H.
  - split; [exact H | constructor].
  - destruct (IH _ H) as [Hb Hl]; apply andb_true_iff in Hb; destruct Hb as [Hb Hy].
    split; [exact Hb | constructor; assumption].
Qed.

Lemma evalExpr_And_true : forall (ls : list (Expr type Bool)),
  evalExpr (And ls) = true -> Forall (fun e : Expr type Bool => evalExpr e = true) ls.
Proof.
  intros ls H; cbn [evalExpr] in H.
  destruct (fold_left_andb_true _ _ H) as [_ Hl].
  apply Forall_map in Hl; exact Hl.
Qed.


Lemma fold_left_orb_true : forall (l : list bool) b,
  fold_left orb l b = true -> b = true \/ Exists (fun x => x = true) l.
Proof.
  induction l as [| y l IH]; intros b H; cbn [fold_left] in H; [left; exact H |].
  destruct (IH _ H) as [Hb | Hl]; [| right; right; exact Hl].
  apply orb_true_iff in Hb; destruct Hb as [Hb | Hy]; [left; exact Hb | right; left; exact Hy].
Qed.

(* The optional tail of the standard fu list. *)
Lemma Forall_optTail : forall A (P : A -> Prop) B (l : list B) (xs : list A),
  Forall P xs -> Forall P (match l with nil => [] | _ :: _ => xs end).
Proof. intros A P B l xs H; destruct l; [constructor | exact H]. Qed.

Lemma map_optTail : forall A A' B (f : A -> A') (l : list B) (xs : list A),
  map f (match l with nil => [] | _ :: _ => xs end) = match l with nil => [] | _ :: _ => map f xs end.
Proof. intros A A' B f l xs; destruct l; reflexivity. Qed.

Lemma In_optTail : forall A B (l : list B) (xs : list A) q,
  In q (match l with nil => [] | _ :: _ => xs end) -> In q xs.
Proof. intros A B l xs q H; destruct l; [destruct H | exact H]. Qed.

Section FUProof.
  Variable F : FpFmt.
  Variable xlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.

  Local Abbreviation PktK := (FpuPktK narrow).
  Local Abbreviation FU := (FU F xlen narrow).
  Local Abbreviation InK := (FUInK F xlen narrow).
  Local Abbreviation OutK := (FUOutK F xlen).

  (* The spec output for an input: destination and result. *)
  Definition fuSpec (x : type InK) : type OutK :=
    (x @% "pkt" @% "rd" ,,
     (execResOf true F xlen narrow (x @% "pkt") (x @% "rm") (x @% "a") (x @% "b") (x @% "c") (x @% "x") ,, tt)).

  Definition acceptsF (L : FU) (pkt : type PktK) : bool := evalExpr (fuAccepts _ _ _ L type pkt).

  Record FUView (L : FU) := mkFUView {
    lvHolds  : TreeState ElemState (fuTree _ _ _ L) -> list (type InK) -> Prop ;
    lvReady  : TreeState ElemState (fuTree _ _ _ L) -> Prop ;
    lvCanEnq : TreeState ElemState (fuTree _ _ _ L) -> Prop
  }.

  Record FUOk (L : FU) (V : FUView L) : Prop := {
    lo_init : forall s, InitStateConsistent (fuTree _ _ _ L) s -> lvHolds L V s [] ;
    lo_canEnq : forall env s Q,
      evalActionPropGen env (fuCanEnq _ _ _ L type) s Q ->
      exists b, Q s b /\ (b = true -> lvCanEnq L V s) ;
    lo_enq : forall env s xs (x : type InK) Q,
      lvHolds L V s xs -> lvCanEnq L V s -> acceptsF L (x @% "pkt") = true ->
      evalActionPropGen env (fuEnq _ _ _ L type x) s Q ->
      exists s', Q s' Zmod.zero /\ lvHolds L V s' (xs ++ [x]) ;
    lo_first : forall env s xs Q,
      lvHolds L V s xs ->
      evalActionPropGen env (fuFirst _ _ _ L type) s Q ->
      exists o, Q s o /\
        (o @% "valid" = true -> exists x rest, xs = x :: rest /\ o @% "data" = fuSpec x /\ lvReady L V s) ;
    lo_deq : forall env s (x : type InK) xs Q,
      lvHolds L V s (x :: xs) -> lvReady L V s ->
      evalActionPropGen env (fuDeq _ _ _ L type) s Q ->
      exists s', Q s' Zmod.zero /\ lvHolds L V s' xs ;
    lo_rules : forall env r s xs Q,
      In r (fuRules _ _ _ L type) -> lvHolds L V s xs ->
      evalActionPropGen env r s Q ->
      exists s', Q s' Zmod.zero /\ lvHolds L V s' xs
  }.

  (* ---------------------------------------------------------------------------
   * 1. THE SPEC RESULT: MAIN OPS AND NARROW CONVERSIONS
   * --------------------------------------------------------------------------- *)

  Definition unboxV (G : FpFmt) (a : bits flen) : bits (fmtW G) :=
    evalExpr (fpUnbox F type G a).

  Definition reqV (op : type FpOpDK) (rm : bits 3) (a b c : bits flen) (x : bits xlen)
    : type (FpReqK (fmtE F) (fmtF F) xlen) :=
    (op ,, (rm ,, (a ,, (b ,, (c ,, (x ,, tt)))))).

  Definition boxV (G : FpFmt) (v : bits (fmtW G)) : bits flen :=
    evalExpr (fpBox F type G (Var type (Bit (fmtW G)) v)).

  Lemma evalExpr_fpBox : forall G (ex : Expr type (Bit (fmtW G))),
    evalExpr (fpBox F type G ex) = boxV G (evalExpr ex).
  Proof.
    intros G ex; unfold boxV, fpBox; cbn [evalExpr fold_left map].
    rewrite (evalExpr_zext_congr _ _ ex (Var type _ (evalExpr ex)) eq_refl); reflexivity.
  Qed.

  Definition opWritesXV (op : type (FpuOpK narrow)) : bool := evalExpr (opWritesXE narrow type op).

  Definition isNarrowV (op : type (FpuOpK narrow)) : bool := evalExpr (isNarrowE narrow type op).

  (* The decoded operation. *)
  Definition decV (op : type (FpuOpK narrow)) : type FpOpDK := evalLetExpr (decodeOp narrow type op).

  (* The result of an ordinary (non-narrow) op. *)
  Definition mainV (op : type (FpuOpK narrow)) (rm : bits 3) (a b c : bits flen) (x : bits xlen) : type (FpuResK F xlen) :=
    let o := evalLetExpr (fpuCompute true (fmtE F) (fmtF F) xlen type (reqV (decV op) rm a b c x)) in
    (o @% "res" ,, (o @% "xres" ,, (o @% "flags" ,, (negb (opWritesXV op) ,, tt)))).

  Lemma fuSpec_main : forall (x : type InK),
    isNarrowV (x @% "pkt" @% "op") = false ->
    fuSpec x = (x @% "pkt" @% "rd" ,,
                (mainV (x @% "pkt" @% "op") (x @% "rm") (x @% "a") (x @% "b") (x @% "c") (x @% "x") ,, tt)).
  Proof.
    intros x Hn.
    unfold fuSpec, execResOf, execCompute, mainRes; cbn [evalLetExpr].
    cbn [evalExpr].
    match goal with |- context [evalExpr (isNarrowE narrow type ?o)] =>
      replace (evalExpr (isNarrowE narrow type o)) with false by (symmetry; exact Hn) end.
    reflexivity.
  Qed.

  (* A narrow conversion: the result is what `cvtOut` computes. *)
  Lemma fuSpec_narrow : forall (x : type InK),
    isNarrowV (x @% "pkt" @% "op") = true ->
    fuSpec x = evalLetExpr (cvtOut F xlen narrow type x).
  Proof.
    intros x Hn.
    unfold fuSpec, execResOf, execCompute, cvtOut; cbn [evalLetExpr].
    cbn [evalExpr].
    match goal with |- context [evalExpr (isNarrowE narrow type ?o)] =>
      replace (evalExpr (isNarrowE narrow type o)) with true by (symmetry; exact Hn) end.
    reflexivity.
  Qed.

  (* Family tests are comparisons of the union's tag (positions in `FpuOpList`). *)
  Lemma isNarrow_tag : forall (op : type (FpuOpK narrow)),
    isNarrowV op = Zmod.eqb op.(Snd) (Zmod.of_Z _ 12).
  Proof. intros; reflexivity. Qed.

  Lemma isDiv_tag : forall (pkt : type PktK),
    evalExpr (isDivP narrow type pkt) = Zmod.eqb (pkt @% "op").(Snd) (Zmod.of_Z _ 3).
  Proof. intros; reflexivity. Qed.

  Lemma isSqrt_tag : forall (pkt : type PktK),
    evalExpr (isSqrtP narrow type pkt) = Zmod.eqb (pkt @% "op").(Snd) (Zmod.of_Z _ 4).
  Proof. intros; reflexivity. Qed.

  Lemma decDiv_tag : forall (op : type (FpuOpK narrow)), (decV op) @% "div" = Zmod.eqb op.(Snd) (Zmod.of_Z _ 3).
  Proof. intros; reflexivity. Qed.

  Lemma decSqrt_tag : forall (op : type (FpuOpK narrow)), (decV op) @% "sqrt" = Zmod.eqb op.(Snd) (Zmod.of_Z _ 4).
  Proof. intros; reflexivity. Qed.

  Lemma isNarrow_pkt : forall (pkt : type PktK), isNarrowV (pkt @% "op") = evalExpr (isCvtNP narrow type pkt).
  Proof. intros; reflexivity. Qed.

  Lemma div_not_narrow : forall (pkt : type PktK),
    evalExpr (isDivP narrow type pkt) = true -> isNarrowV (pkt @% "op") = false.
  Proof. intros pkt H; rewrite isDiv_tag in H; apply Zmod.eqb_eq in H; rewrite isNarrow_tag, H; reflexivity. Qed.

  Lemma sqrt_not_narrow : forall (pkt : type PktK),
    evalExpr (isSqrtP narrow type pkt) = true -> isNarrowV (pkt @% "op") = false.
  Proof. intros pkt H; rewrite isSqrt_tag in H; apply Zmod.eqb_eq in H; rewrite isNarrow_tag, H; reflexivity. Qed.

  (* A narrow conversion's result goes to an f register. *)
  Lemma narrow_not_writesX : forall (op : type (FpuOpK narrow)), isNarrowV op = true -> opWritesXV op = false.
  Proof. intros [d t] H; rewrite isNarrow_tag in H; apply Zmod.eqb_eq in H; cbn [Snd] in H; subst t; reflexivity. Qed.

  (* `narrowSel` writes an f register if the index names an entry (or the default does). *)
  Lemma narrowSel_wf : forall (toN : bool) (rm : bits 3) (a : bits flen) (nidx : bits (NIdxSz narrow))
    (gs : list FpFmt) (k : nat) (acc : type (FpuResK F xlen)),
    (acc @% "writesF" = true \/
     Exists (fun j : nat => evalExpr (Eq (Var type (Bit (NIdxSz narrow)) nidx) (cst (NIdxSz narrow) (Z.of_nat j))) = true)
            (seq k (length gs))) ->
    (evalLetExpr (narrowSel true F xlen narrow type toN rm a nidx gs k acc)) @% "writesF" = true.
  Proof.
    intros toN rm a nidx gs; induction gs as [| G rest IH]; intros k acc H.
    - destruct H as [H | H]; [exact H | inversion H].
    - cbn [narrowSel evalLetExpr]; apply IH.
      cbn [length seq] in H.
      match goal with |- context [evalExpr (ITE ?c (Var _ _ ?blk) (Var _ _ ?acc0))] =>
        change (evalExpr (ITE c (Var type _ blk) (Var type _ acc0))) with (if evalExpr c then blk else acc0) end.
      destruct (evalExpr (Eq (Var type (Bit (NIdxSz narrow)) nidx) (cst (NIdxSz narrow) (Z.of_nat k)))) eqn:E.
      + left; unfold narrowBlock; cbn [evalLetExpr]; reflexivity.
      + destruct H as [H | H]; [left; exact H |].
        apply Exists_cons in H; destruct H as [H | H]; [rewrite H in E; discriminate E | right; exact H].
  Qed.

  (* ---------------------------------------------------------------------------
   * 2. METADATA WRAPPER
   * --------------------------------------------------------------------------- *)

  Definition metaV (x : type InK) : type FUMetaK := evalLetExpr (fuMetaOf F xlen narrow type x).

  Section WithMetaLemmas.
    Variable SK OK : Kind.
    Variable initU   : forall ty, ty (FpReqK (fmtE F) (fmtF F) xlen) -> LetExpr ty SK.
    Variable stepU   : forall ty, ty SK -> LetExpr ty SK.
    Variable finishU : forall ty, ty SK -> LetExpr ty OK.
    Variable resU    : forall ty, ty OK -> Expr ty (FpResK (fmtE F) (fmtF F) xlen).

    Definition reqOfV (x : type InK) : type (FpReqK (fmtE F) (fmtF F) xlen) :=
      reqV (decV (x @% "pkt" @% "op")) (x @% "rm") (x @% "a") (x @% "b") (x @% "c") (x @% "x").

    Lemma SV_withMeta : forall k (x : type InK),
      StageValAt (withMetaInit F xlen narrow SK initU) (withMetaStep SK stepU) k x =
      (metaV x ,, (StageValAt initU stepU k (reqOfV x) ,, tt)).
    Proof.
      induction k as [| k IH]; intros x; cbn [StageValAt]; [reflexivity |].
      rewrite IH; reflexivity.
    Qed.

    Lemma withMetaFinish_eval : forall (m : type FUMetaK) (sv : type SK),
      evalLetExpr (withMetaFinish F xlen SK OK finishU resU type (m ,, (sv ,, tt))) =
      (let r := evalExpr (resU type (evalLetExpr (finishU type sv))) in
       (m @% "rd" ,, ((r @% "res" ,,
                       (r @% "xres" ,, (r @% "flags" ,, (m @% "wf" ,, tt)))) ,, tt))).
    Proof. intros; reflexivity. Qed.
  End WithMetaLemmas.

  (* Facts from acceptance. *)
  Lemma evalExpr_Not_true : forall (ex : Expr type Bool), evalExpr (Not ex) = true -> evalExpr ex = false.
  Proof. intros ex H; cbn [evalExpr evalNot KindCustomInd] in H; destruct (evalExpr ex); [discriminate | reflexivity]. Qed.


  (* ---------------------------------------------------------------------------
   * 3. EACH FU COMPUTES THE SPEC
   * --------------------------------------------------------------------------- *)

  Definition PipeCfgOk (ms bps : nat) : Prop :=
    (0 < ms * bps)%nat /\ 0 <= fmtF F /\ fmtF F + 1 <= IntMul.dataLen (ms * bps).

  Lemma pipeFU_spec : forall ms bps (x : type InK),
    PipeCfgOk ms bps ->
    acceptsF (pipeFU F xlen narrow ms bps) (x @% "pkt") = true ->
    evalLetExpr (plFinish F xlen ms bps type
                   (StageValAt (plInit F xlen narrow ms bps) (plStep F xlen ms bps) ms x)) =
    fuSpec x.
  Proof.
    intros ms bps x [Hmw [Hf Hfit]] Hacc.
    unfold acceptsF in Hacc; cbn [fuAccepts pipeFU] in Hacc.
    apply evalExpr_And_true in Hacc.
    inversion Hacc as [| ? ? Hdiv Hacc1]; subst; clear Hacc.
    inversion Hacc1 as [| ? ? Hsqrt Hacc2]; subst; clear Hacc1.
    inversion Hacc2 as [| ? ? Hn _]; subst; clear Hacc2.
    apply evalExpr_Not_true in Hdiv, Hsqrt, Hn.
    rewrite (fuSpec_main x Hn); unfold mainV.
    unfold plFinish, plInit, plStep; rewrite SV_withMeta, withMetaFinish_eval.
    unfold resId; cbn zeta.
    rewrite (Pipe_StageValAt_spec (fmtE F) (fmtF F) xlen ms bps Hmw Hf Hfit).
    rewrite fpuCompute_dispatch.
    rewrite isDiv_tag in Hdiv; rewrite isSqrt_tag in Hsqrt.
    match goal with |- context [?r @% "op" @% "div"] =>
      replace (r @% "op" @% "div") with false
        by (symmetry; change ((decV (x @% "pkt" @% "op")) @% "div" = false); rewrite decDiv_tag; exact Hdiv) end.
    match goal with |- context [?r @% "op" @% "sqrt"] =>
      replace (r @% "op" @% "sqrt") with false
        by (symmetry; change ((decV (x @% "pkt" @% "op")) @% "sqrt" = false); rewrite decSqrt_tag; exact Hsqrt) end.
    reflexivity.
  Qed.

  Lemma divFU_spec : forall (x : type InK),
    0 <= fmtF F ->
    acceptsF (divFU F xlen narrow) (x @% "pkt") = true ->
    evalLetExpr (dlFinish F xlen type (StageValAt (dlInit F xlen narrow) (dlStep F) (divSteps (fmtF F)) x)) =
    fuSpec x.
  Proof.
    intros x Hf Hacc.
    unfold acceptsF in Hacc; cbn [fuAccepts divFU] in Hacc.
    rewrite (fuSpec_main x (div_not_narrow _ Hacc)); unfold mainV.
    rewrite isDiv_tag in Hacc.
    unfold dlFinish, dlInit, dlStep; rewrite SV_withMeta, withMetaFinish_eval.
    unfold resOut; cbn zeta.
    rewrite (Div_StageValAt_spec (fmtE F) (fmtF F) xlen Hf).
    rewrite fpuCompute_dispatch.
    match goal with |- context [?r @% "op" @% "div"] =>
      replace (r @% "op" @% "div") with true
        by (symmetry; change ((decV (x @% "pkt" @% "op")) @% "div" = true); rewrite decDiv_tag; exact Hacc) end.
    reflexivity.
  Qed.

  Lemma sqrtFU_spec : forall (x : type InK),
    acceptsF (sqrtFU F xlen narrow) (x @% "pkt") = true ->
    evalLetExpr (slFinish F xlen type (StageValAt (slInit F xlen narrow) (slStep F) (sqrtSteps (fmtF F)) x)) =
    fuSpec x.
  Proof.
    intros x Hacc.
    unfold acceptsF in Hacc; cbn [fuAccepts sqrtFU] in Hacc.
    rewrite (fuSpec_main x (sqrt_not_narrow _ Hacc)); unfold mainV.
    rewrite isSqrt_tag in Hacc; pose proof Hacc as Hop; apply Zmod.eqb_eq in Hop.
    unfold slFinish, slInit, slStep; rewrite SV_withMeta, withMetaFinish_eval.
    unfold resOut; cbn zeta.
    rewrite (Sqrt_StageValAt_spec (fmtE F) (fmtF F) xlen).
    rewrite fpuCompute_dispatch.
    match goal with |- context [?r @% "op" @% "div"] =>
      replace (r @% "op" @% "div") with false
        by (symmetry; change ((decV (x @% "pkt" @% "op")) @% "div" = false); rewrite decDiv_tag, Hop; reflexivity) end.
    match goal with |- context [?r @% "op" @% "sqrt"] =>
      replace (r @% "op" @% "sqrt") with true
        by (symmetry; change ((decV (x @% "pkt" @% "op")) @% "sqrt" = true); rewrite decSqrt_tag; exact Hacc) end.
    reflexivity.
  Qed.

  Lemma cvtFU_spec : forall (x : type InK),
    acceptsF (cvtFU F xlen narrow) (x @% "pkt") = true ->
    evalLetExpr (cvtOut F xlen narrow type x) = fuSpec x.
  Proof.
    intros x Hacc.
    unfold acceptsF in Hacc; cbn [fuAccepts cvtFU] in Hacc.
    apply evalExpr_And_true in Hacc.
    inversion Hacc as [| ? ? Hop _]; subst; clear Hacc.
    symmetry; apply fuSpec_narrow; rewrite isNarrow_pkt; exact Hop.
  Qed.

  (* An accepted narrow conversion writes an f register. *)
  Lemma cvtFU_wf : forall (x : type InK),
    acceptsF (cvtFU F xlen narrow) (x @% "pkt") = true ->
    (fuSpec x) @% "res" @% "writesF" = true.
  Proof.
    intros x Hacc.
    rewrite <- (cvtFU_spec x Hacc).
    unfold acceptsF in Hacc; cbn [fuAccepts cvtFU] in Hacc.
    apply evalExpr_And_true in Hacc.
    inversion Hacc as [| ? ? _ Hacc1]; subst; clear Hacc.
    inversion Hacc1 as [| ? ? Hn _]; subst; clear Hacc1.
    unfold nidxOk in Hn; cbn [evalExpr evalOrBinary evalBinary KindCustomInd getDefault] in Hn.
    destruct (fold_left_orb_true _ _ Hn) as [Hf | Hex]; [discriminate Hf |].
    rewrite map_map, Exists_map in Hex.
    unfold cvtOut; cbn [evalLetExpr].
    apply narrowSel_wf; right; exact Hex.
  Qed.

  (* ---------------------------------------------------------------------------
   * 4. FU CORRECTNESS
   * --------------------------------------------------------------------------- *)

  Definition AllAcc (L : FU) (xs : list (type InK)) : Prop :=
    Forall (fun x : type InK => acceptsF L (x @% "pkt") = true) xs.

  Lemma AllAcc_app1 : forall L xs (x : type InK), AllAcc L xs -> acceptsF L (x @% "pkt") = true -> AllAcc L (xs ++ [x]).
  Proof. intros; apply Forall_app; split; [assumption | constructor; [assumption | constructor]]. Qed.

  Section PipeFUOk.
    Variable ms bps : nat.
    Local Abbreviation L := (pipeFU F xlen narrow ms bps).
    Local Abbreviation SK := (WithMetaK (PipeStateK (fmtE F) (fmtF F) xlen (ms * bps))).

    Definition pipeFUView : FUView L := mkFUView L
      (fun s xs => PipeHolds InK SK (plInit F xlen narrow ms bps) (plStep F xlen ms bps) 0 ms s xs /\ AllAcc L xs)
      (fun s => PipeReady SK ms s)
      (fun s => fifoVal s.(Fst) = None).

    Lemma pipeFU_ok : PipeCfgOk ms bps -> FUOk L pipeFUView.
    Proof.
      intros Hcfg.
      constructor; cbn [lvHolds lvReady lvCanEnq pipeFUView fuCanEnq fuEnq fuFirst fuDeq fuRules pipeFU fuTree].
      - intros s Hi; split; [apply PipeHolds_init; exact Hi | constructor].
      - intros env s Q H; rewrite evalActionPropGen_pipeCanEnq in H.
        eexists; split; [exact H | apply pipeCanEnq_empty].
      - intros env s xs x Q [Hh Ha] Hc Hx H.
        destruct (pipeEnq_fwd _ _ _ _ _ s xs x Q Hh Hc H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; [exact Hh' | apply AllAcc_app1; assumption]].
      - intros env s xs Q [Hh Ha] H.
        destruct (pipeFirst_fwd _ _ _ _ _ _ _ s xs Q Hh H) as [o [HQ Ho]].
        exists o; split; [exact HQ |]; intros Hv.
        destruct (Ho Hv) as [x [rest [-> [Hd Hr]]]].
        exists x, rest; split; [reflexivity | split; [| exact Hr]].
        rewrite Hd; inversion Ha; subst; apply pipeFU_spec; assumption.
      - intros env s x xs Q [Hh Ha] Hr H.
        destruct (pipeDeq_fwd _ _ _ _ _ s x xs Q Hh Hr H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; [exact Hh' | inversion Ha; assumption]].
      - intros env r s xs Q Hr [Hh Ha] H.
        destruct (pipeRules_fwd _ _ _ _ ms 0 r s xs Q Hr Hh H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; assumption].
    Qed.
  End PipeFUOk.

  Lemma IterHolds_single : forall InpK StateK n numStepsFn initFn stepFn s (x : type InpK) xs,
    IterHolds InpK StateK n numStepsFn initFn stepFn s (x :: xs) -> xs = [].
  Proof.
    intros InpK StateK n numStepsFn initFn stepFn s x xs [[_ H] | [y [m [H _]]]]; [discriminate | injection H; auto].
  Qed.

  Lemma iterCanEnq_idle : forall StateK n (s : TreeState ElemState (stagedIterTree StateK n)),
    negb (s @% "busy") = true -> s @% "busy" = false.
  Proof. intros StateK n s H; destruct (s @% "busy"); [discriminate | reflexivity]. Qed.

  Section DivFUOk.
    Local Abbreviation L := (divFU F xlen narrow).
    Local Abbreviation n := (divSteps (fmtF F)).
    Local Abbreviation SK := (WithMetaK (DivStateK (fmtE F) (fmtF F))).

    Definition divFUView : FUView L := mkFUView L
      (fun s xs => IterHolds InK SK n (dlSteps F xlen narrow) (dlInit F xlen narrow) (dlStep F) s xs /\ AllAcc L xs)
      (fun s => IterReady SK n s)
      (fun s => s @% "busy" = false).

    Lemma dl_target : forall x, IterTargetSteps InK n (dlSteps F xlen narrow) x = n.
    Proof. intros x; unfold IterTargetSteps, dlSteps; cbn [evalLetExpr evalExpr]; apply iterStepsSz_unsigned_nat; lia. Qed.

    Lemma divFU_ok : 0 <= fmtF F -> FUOk L divFUView.
    Proof.
      intros Hf.
      constructor; cbn [lvHolds lvReady lvCanEnq divFUView fuCanEnq fuEnq fuFirst fuDeq fuRules divFU fuTree].
      - intros s Hi; split; [apply IterHolds_init; exact Hi | constructor].
      - intros env s Q H; rewrite evalActionPropGen_iterCanEnq in H.
        eexists; split; [exact H | apply iterCanEnq_idle].
      - intros env s xs x Q [Hh Ha] Hc Hx H.
        destruct (iterEnq_fwd _ _ _ _ _ _ s xs x Q Hh Hc H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; [exact Hh' | apply AllAcc_app1; assumption]].
      - intros env s xs Q [Hh Ha] H.
        destruct (iterFirst_fwd _ _ _ _ _ _ _ _ s xs Q Hh H) as [o [HQ Ho]].
        exists o; split; [exact HQ |]; intros Hv.
        destruct (Ho Hv) as [x [-> [Hd Hr]]].
        exists x, []; split; [reflexivity | split; [| exact Hr]].
        rewrite Hd, dl_target; inversion Ha; subst; apply divFU_spec; assumption.
      - intros env s x xs Q [Hh Ha] Hr H.
        pose proof (IterHolds_single _ _ _ _ _ _ _ _ _ Hh) as ->.
        destruct (iterDeq_fwd _ _ _ _ _ _ s x Q Hh Hr H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; [exact Hh' | constructor]].
      - intros env r s xs Q Hr [Hh Ha] H.
        destruct Hr as [<- | []].
        destruct (iterStep_fwd _ _ _ _ _ _ s xs Q Hh H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; assumption].
    Qed.
  End DivFUOk.

  Section SqrtFUOk.
    Local Abbreviation L := (sqrtFU F xlen narrow).
    Local Abbreviation n := (sqrtSteps (fmtF F)).
    Local Abbreviation SK := (WithMetaK (SqrtStateK (fmtE F) (fmtF F))).

    Definition sqrtFUView : FUView L := mkFUView L
      (fun s xs => IterHolds InK SK n (slSteps F xlen narrow) (slInit F xlen narrow) (slStep F) s xs /\ AllAcc L xs)
      (fun s => IterReady SK n s)
      (fun s => s @% "busy" = false).

    Lemma sl_target : forall x, IterTargetSteps InK n (slSteps F xlen narrow) x = n.
    Proof. intros x; unfold IterTargetSteps, slSteps; cbn [evalLetExpr evalExpr]; apply iterStepsSz_unsigned_nat; lia. Qed.

    Lemma sqrtFU_ok : FUOk L sqrtFUView.
    Proof.
      constructor; cbn [lvHolds lvReady lvCanEnq sqrtFUView fuCanEnq fuEnq fuFirst fuDeq fuRules sqrtFU fuTree].
      - intros s Hi; split; [apply IterHolds_init; exact Hi | constructor].
      - intros env s Q H; rewrite evalActionPropGen_iterCanEnq in H.
        eexists; split; [exact H | apply iterCanEnq_idle].
      - intros env s xs x Q [Hh Ha] Hc Hx H.
        destruct (iterEnq_fwd _ _ _ _ _ _ s xs x Q Hh Hc H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; [exact Hh' | apply AllAcc_app1; assumption]].
      - intros env s xs Q [Hh Ha] H.
        destruct (iterFirst_fwd _ _ _ _ _ _ _ _ s xs Q Hh H) as [o [HQ Ho]].
        exists o; split; [exact HQ |]; intros Hv.
        destruct (Ho Hv) as [x [-> [Hd Hr]]].
        exists x, []; split; [reflexivity | split; [| exact Hr]].
        rewrite Hd, sl_target; inversion Ha; subst; apply sqrtFU_spec; assumption.
      - intros env s x xs Q [Hh Ha] Hr H.
        pose proof (IterHolds_single _ _ _ _ _ _ _ _ _ Hh) as ->.
        destruct (iterDeq_fwd _ _ _ _ _ _ s x Q Hh Hr H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; [exact Hh' | constructor]].
      - intros env r s xs Q Hr [Hh Ha] H.
        destruct Hr as [<- | []].
        destruct (iterStep_fwd _ _ _ _ _ _ s xs Q Hh H) as [s' [HQ Hh']].
        exists s'; split; [exact HQ | split; assumption].
    Qed.
  End SqrtFUOk.

  Section CvtFUOk.
    Local Abbreviation L := (cvtFU F xlen narrow).

    Definition cvtFUView : FUView L := mkFUView L
      (fun s xs => match fifoVal s with
                   | None => xs = []
                   | Some o => exists x, xs = [x] /\ o = fuSpec x
                   end)
      (fun s => fifoVal s <> None)
      (fun s => fifoVal s = None).

    Lemma cvtFU_ok : FUOk L cvtFUView.
    Proof.
      constructor; cbn [lvHolds lvReady lvCanEnq cvtFUView fuCanEnq fuEnq fuFirst fuDeq fuRules cvtFU fuTree].
      - intros [[e []] [sz []]] Hi; cbn in Hi; destruct Hi as [_ [Hsz _]].
        rewrite fifoVal_empty; [reflexivity | unfold fifo1_size; cbn [Fst Snd] in *; rewrite Hsz; reflexivity].
      - intros env s Q H; cbn [evalActionPropGen] in H; rewrite evalActionPropGen_fifo_isFull in H; cbn [evalActionPropGen] in H.
        eexists; split; [exact H | apply pipeCanEnq_empty].
      - intros env s xs x Q Hh Hc Hx H.
        cbn [evalActionPropGen] in H; rewrite evalActionPropGen_toAction, evalActionPropGen_fifo_enq in H.
        rewrite (fifoVal_None_size _ Hc) in H.
        change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false in H; cbn [negb] in H.
        eexists; split; [exact H |].
        rewrite Hc in Hh; subst xs.
        rewrite fifoVal_full by reflexivity.
        exists x; split; [reflexivity |]; unfold fifo1_elem, mkFifo1; cbn [Fst Snd].
        apply cvtFU_spec; exact Hx.
      - intros env s xs Q Hh H; rewrite evalActionPropGen_fifo_first in H.
        eexists; split; [exact H |].
        destruct (bits1_cases (fifo1_size s)) as [Hs | Hs]; rewrite Hs.
        + change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 0)) with true; cbn; discriminate.
        + change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; intros _.
          rewrite (fifoVal_full s Hs) in Hh |- *; destruct Hh as [x [-> Hx]].
          exists x, []; split; [reflexivity | split; [exact Hx | discriminate]].
      - intros env s x xs Q Hh Hr H; rewrite evalActionPropGen_fifo_deq in H.
        destruct (bits1_cases (fifo1_size s)) as [Hs | Hs]; [rewrite (fifoVal_empty s Hs) in Hr; contradiction |].
        rewrite Hs in H; change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false in H; cbn [negb] in H.
        eexists; split; [exact H |].
        rewrite (fifoVal_full s Hs) in Hh; destruct Hh as [y [Hy _]]; injection Hy as _ ->.
        rewrite fifoVal_empty by reflexivity; reflexivity.
      - intros env r s xs Q [].
    Qed.
  End CvtFUOk.

  (* ---------------------------------------------------------------------------
   * 5. THE STANDARD FUS
   * --------------------------------------------------------------------------- *)

  Record FUP := mkFUP { fuL : FU ; fuV : FUView fuL }.

  Definition fpuFUsP (ms bps : nat) : list FUP :=
    [ mkFUP _ (pipeFUView ms bps) ; mkFUP _ divFUView ; mkFUP _ sqrtFUView ]
    ++ (match narrow with nil => [] | _ => [ mkFUP _ cvtFUView ] end).

  Lemma fpuFUsP_fus : forall ms bps, map fuL (fpuFUsP ms bps) = fpuFUs F xlen narrow ms bps.
  Proof. intros; unfold fpuFUsP, fpuFUs; rewrite map_app, map_optTail; reflexivity. Qed.

  Lemma fpuFUsP_ok : forall ms bps, PipeCfgOk ms bps ->
    Forall (fun p => FUOk (fuL p) (fuV p)) (fpuFUsP ms bps).
  Proof.
    intros ms bps Hc; pose proof Hc as [_ [Hf _]].
    unfold fpuFUsP; apply Forall_app; split.
    - constructor; [apply pipeFU_ok; exact Hc |].
      constructor; [apply divFU_ok; exact Hf |].
      constructor; [apply sqrtFU_ok | constructor].
    - apply Forall_optTail; constructor; [apply cvtFU_ok | constructor].
  Qed.
End FUProof.
