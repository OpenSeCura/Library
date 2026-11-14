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
 * Standalone refinement of the pipelined FPU by the atomic FPU (`FpuRefinement.v`), the first
 * client of the lemmas of `RelFpu.v`:
 *
 *   `fpu_refines` : ModSimulationInit (fpuImplMod ... fus) (fpuSpecMod ...) RelFpu _
 *
 * Every impl step (internal rule or driver call) is matched by committing, in program order,
 * the longest done prefix of the ghost (`commit_prefix`): each committed entry is one spec rule
 * (`spec_entry_step`).  `fpu_refines_std` instantiates it with the standard fus.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Arith.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Fpu Require Import FpUtil FpCore FpuArch SpecFpu FpuFU ImplFpu.
From Fpu Require Import FpuArchLemmas SpecFpuLemmas FpuFUProof BitVecLemmas ImplFpuLemmas RelFpu.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Open Scope list_scope.

Section Refinement.
  (* Exponent mode of the spec's core.  Every result the spec computes goes through `execResOf`;
   * the proof only needs it to agree with the biased model (`true`), which the units implement. *)
  Variable bm : bool.
  Variable F : FpFmt.
  Variable xlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.
  Hypothesis H_bm : forall pkt rm a b c x,
    execResOf bm F xlen narrow pkt rm a b c x = execResOf true F xlen narrow pkt rm a b c x.

  Local Abbreviation St := (ArchSt flen).
  Local Abbreviation ST := (fpuArchTree flen).

  (* ---------------------------------------------------------------------------
   * 1. EACH DONE ENTRY IS ONE SPEC RULE
   * --------------------------------------------------------------------------- *)

  Lemma execSem_entry : forall (s : St) pkt xv i d,
    execSem bm F xlen narrow s pkt xv = entrySem F xlen narrow (EExec F xlen narrow (inpOf F xlen narrow s pkt xv) i d) s.
  Proof. intros; unfold execSem, execRes; rewrite H_bm; exact eq_refl. Qed.

  Lemma spec_entry_step : forall (env : Env ST) (s : St) e g,
    Cons F xlen narrow s (e :: g) -> doneE F xlen narrow e = true ->
    exists a, In a (fpuSpecRules bm F xlen narrow type) /\ SemAction env a s (entrySem F xlen narrow e s) Zmod.zero.
  Proof.
    intros env s e g [Hok _] Hd.
    set (P := fun (s' : St) (r : type (Bit 0)) => s' = entrySem F xlen narrow e s /\ r = Zmod.zero).
    assert (H : exists a, In a (fpuSpecRules bm F xlen narrow type) /\ evalActionPropGen env a s P).
    { destruct e as [x i [|] | rd [v |] | rd v | v | v | v | v]; cbn [doneE] in Hd; try discriminate.
      - eexists; split; [left; reflexivity |]; cbn [evalActionPropGen].
        exists (x @% "pkt"), (x @% "x").
        rewrite evalActionPropGen_fpuExec; cbn [evalActionPropGen]; split; [| apply bits0_eq].
        pose proof (execSem_entry s (x @% "pkt") (x @% "x") i true) as E; cbn [entryOk] in Hok.
        rewrite <- Hok in E; exact E.
      - eexists; split; [right; left; reflexivity |]; cbn [evalActionPropGen].
        exists rd, v; rewrite evalActionPropGen_fpuWrite; split; reflexivity.
      - eexists; split; [right; left; reflexivity |]; cbn [evalActionPropGen].
        exists rd, v; rewrite evalActionPropGen_fpuWrite; split; reflexivity.
      - eexists; split; [right; right; left; reflexivity |]; cbn [evalActionPropGen].
        exists v; rewrite evalActionPropGen_frmWrite; split; reflexivity.
      - eexists; split; [right; right; right; left; reflexivity |]; cbn [evalActionPropGen].
        exists v; rewrite evalActionPropGen_fflagsWrite; split; reflexivity.
      - eexists; split; [right; right; right; right; left; reflexivity |]; cbn [evalActionPropGen].
        exists v; rewrite evalActionPropGen_fcsrWrite; split; reflexivity.
      - eexists; split; [right; right; right; right; right; left; reflexivity |]; cbn [evalActionPropGen].
        exists v; rewrite evalActionPropGen_fsWrite; split; reflexivity. }
    destruct H as [a [Hin Ha]]; exists a; split; [exact Hin |].
    destruct (evalActionPropGen_to_SemAction a s P Ha) as [s' [r [Hsem [-> ->]]]]; exact Hsem.
  Qed.

  Variable lps : list (FUP F xlen narrow).
  Local Abbreviation ls := (map (fuL F xlen narrow) lps).
  Local Abbreviation IT := (implTree F xlen narrow ls).
  Local Abbreviation ImplSt := (TreeState ElemState IT).

  (* ---------------------------------------------------------------------------
   * 2. COMMITTING THE DONE PREFIX
   * --------------------------------------------------------------------------- *)

  Lemma commit_prefix : forall (env : Env ST) g (S : ImplSt) sigma,
    RelFpuG F xlen narrow lps g S sigma ->
    exists g' sigma', SemActions env (fpuSpecRules bm F xlen narrow type) sigma sigma' /\
      RelFpuG F xlen narrow lps g' S sigma' /\
      (forall e rest, g' = e :: rest -> doneE F xlen narrow e = false).
  Proof.
    intros env; induction g as [| e g IH]; intros S sigma H.
    - exists [], sigma; split; [constructor; reflexivity | split; [exact H | discriminate]].
    - destruct (doneE F xlen narrow e) eqn:Hd.
      + assert (Hc : Cons F xlen narrow sigma (e :: g))
          by (destruct H as [A [p [lp [ib [Ls [_ HR]]]]]]; exact (r_cons _ _ _ _ _ _ _ _ _ _ _ HR)).
        destruct (spec_entry_step env sigma e g Hc Hd) as [a [Hin Hsem]].
        destruct (IH S _ (rel_commit F xlen narrow lps e g S sigma H Hd)) as [g' [sigma' [Hs [HR Hh]]]].
        exists g', sigma'; split; [econstructor; [exact Hin | exact Hsem | exact Hs] | split; [exact HR | exact Hh]].
      + exists (e :: g), sigma; split; [constructor; reflexivity | split; [exact H |]].
        intros e' rest Heq; injection Heq as <- _; exact Hd.
  Qed.

  (* ---------------------------------------------------------------------------
   * 3. EVERY IMPL STEP
   * --------------------------------------------------------------------------- *)

  Hypothesis H_fus : Forall (FUOkP F xlen narrow) lps.
  Hypothesis H_wf : FUsWf F xlen narrow lps.

  Lemma impl_step_ghost : forall (env : Env IT) a (S S' : ImplSt) sigma,
    In a (fpuImplMod F xlen narrow ls type) -> SemAction env a S S' Zmod.zero ->
    RelFpu F xlen narrow lps S sigma -> RelFpu F xlen narrow lps S' sigma.
  Proof.
    intros env a S S' sigma Hin Hsem [g H].
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    set (P := fun (s : ImplSt) (r : type (Bit 0)) => s = S' /\ r = Zmod.zero) in Hev.
    unfold fpuImplMod in Hin; apply in_app_or in Hin; destruct Hin as [Hin | Hin].
    - destruct (rel_rules F xlen narrow lps H_fus env g S sigma a P H Hin Hev) as [S2 [[-> _] HR]]; exact HR.
    - unfold fpuDriverRules in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [evalActionPropGen] in Hev | ]); try destruct Hin.
      + destruct Hev as [pkt [xv Hev]].
        destruct (rel_issue F xlen narrow lps H_fus H_wf env g S sigma pkt xv _ H Hev) as [S2 [ok [HQ [Hf Ht]]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _].
        destruct ok; [destruct (Ht eq_refl) as [i HR]; eexists; exact HR | destruct (Hf eq_refl) as [-> HR]; eexists; exact HR].
      + destruct (rel_intResp F xlen narrow lps H_fus env g S sigma _ H Hev) as [S2 [r [HQ [Hf Ht]]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _].
        destruct (r @% "valid") eqn:Hv.
        * destruct (Ht eq_refl) as [pre [post [x [i [_ [_ HR]]]]]]; eexists; exact HR.
        * destruct (Hf eq_refl) as [-> HR]; eexists; exact HR.
      + destruct Hev as [rd Hev].
        destruct (rel_reserve F xlen narrow lps env g S sigma rd _ H Hev) as [S2 [ok [HQ HR]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _]; eexists; exact HR.
      + destruct Hev as [rd [v Hev]].
        destruct (rel_fill F xlen narrow lps env g S sigma rd v _ H Hev) as [S2 [ok [HQ [Hf Ht]]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _].
        destruct ok; [destruct (Ht eq_refl) as [pre [post [_ HR]]]; eexists; exact HR | eexists; exact (Hf eq_refl)].
      + destruct Hev as [i [v Hev]].
        destruct (rel_writeT F xlen narrow lps env g S sigma i v _ H Hev) as [S2 [ok [HQ HR]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _]; eexists; exact HR.
      + destruct Hev as [v Hev].
        destruct (rel_frmWrite F xlen narrow lps env g S sigma v _ H Hev) as [S2 [[-> _] HR]]; eexists; exact HR.
      + destruct Hev as [v Hev].
        destruct (rel_fflagsWriteT F xlen narrow lps env g S sigma v _ H Hev) as [S2 [ok [HQ HR]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _]; eexists; exact HR.
      + destruct Hev as [v Hev].
        destruct (rel_fcsrWriteT F xlen narrow lps env g S sigma v _ H Hev) as [S2 [ok [HQ HR]]].
        cbn [evalActionPropGen] in HQ; destruct HQ as [-> _]; eexists; exact HR.
      + destruct Hev as [v Hev].
        destruct (rel_fsWrite F xlen narrow lps env g S sigma v _ H Hev) as [S2 [[-> _] HR]]; eexists; exact HR.
  Qed.

  Lemma impl_step_sim : forall (env1 : Env IT) (env2 : Env ST) a (S S' : ImplSt) sigma,
    In a (fpuImplMod F xlen narrow ls type) -> SemAction env1 a S S' Zmod.zero ->
    RelFpu F xlen narrow lps S sigma ->
    exists sigma', SemActions env2 (fpuSpecMod bm F xlen narrow type) sigma sigma' /\ RelFpu F xlen narrow lps S' sigma'.
  Proof.
    intros env1 env2 a S S' sigma Hin Hsem H.
    destruct (impl_step_ghost env1 a S S' sigma Hin Hsem H) as [g Hg].
    destruct (commit_prefix env2 g S' sigma Hg) as [g' [sigma' [Hs [HR _]]]].
    exists sigma'; split; [exact Hs | exists g'; exact HR].
  Qed.

  (* ---------------------------------------------------------------------------
   * 4. INITIAL STATES
   * --------------------------------------------------------------------------- *)

  Lemma fus_init : forall l (Ls : TreeState ElemState (fusTree F xlen narrow (map (fuL F xlen narrow) l))),
    Forall (FUOkP F xlen narrow) l ->
    InitStateConsistent (fusTree F xlen narrow (map (fuL F xlen narrow) l)) Ls ->
    FUsHold F xlen narrow l Ls (fun _ => []).
  Proof.
    induction l as [| q l IH]; intros Ls Hok Hi; [exact I |].
    apply Forall_cons_iff in Hok; destruct Hok as [Hq Hl].
    destruct Ls as [sq [sl []]]; cbn [map fusTree InitStateConsistent] in Hi; destruct Hi as [Hiq [Hil _]].
    split; [exact (lo_init _ _ _ _ _ Hq sq Hiq) | exact (IH sl Hl Hil)].
  Qed.

  Lemma arch_init_det : allTreeInitDet ST = true.
  Proof. reflexivity. Qed.

  Lemma rel_init : forall (S : ImplSt) (sigma : St),
    InitStateConsistent IT S -> InitStateConsistent ST sigma -> RelFpu F xlen narrow lps S sigma.
  Proof.
    intros [A [[p [lp [ib []]]] [Ls []]]] sigma HS Hs.
    cbn [implTree InitStateConsistent] in HS; destruct HS as [HA [[Hp [Hlp [Hib _]]] [HL _]]].
    cbn in Hp, Hlp, Hib; subst p lp ib.
    pose proof (allTreeInitDet_InitStateConsistent_eq ST A sigma arch_init_det HA Hs) as ->.
    exists [], sigma, Zmod.zero, Zmod.zero, false, Ls; split; [reflexivity |].
    constructor; try reflexivity; try exact I; try (intros r; apply bitOf_zero); try (intros x i d []);
      try exact (fus_init lps Ls H_fus HL).
    cbn [foldSem fold_left pendFlags fold_right]; rewrite bits_or_0_r; reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
   * 5. THE REFINEMENT
   * --------------------------------------------------------------------------- *)

  Theorem fpu_refines : forall (env1 : Env IT) (env2 : Env ST),
    ModSimulationInit env1 env2 (fpuImplMod F xlen narrow ls) (fpuSpecMod bm F xlen narrow)
      (RelFpu F xlen narrow lps) rel_init.
  Proof.
    intros env1 env2.
    apply ActionToActionsModSimulationInit.
    intros a S S' Hin Hsem sigma H; exact (impl_step_sim env1 env2 a S S' sigma Hin Hsem H).
  Qed.
End Refinement.

(* ---------------------------------------------------------------------------
 * 6. THE STANDARD FUS
 * --------------------------------------------------------------------------- *)

Section Standard.
  Variable F : FpFmt.
  Variable xlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.
  Variable ms bps : nat.
  Hypothesis H_cfg : PipeCfgOk F ms bps.

  Local Abbreviation InK := (FUInK F xlen narrow).
  Local Abbreviation lpsStd := (fpuFUsP F xlen narrow ms bps).

  Lemma mainV_writesF : forall op rm a b c x,
    (mainV F xlen narrow op rm a b c x) @% "writesF" = negb (opWritesXV narrow op).
  Proof. intros; reflexivity. Qed.

  (* A non-narrow op writes an f register iff it does not write an x register. *)
  Lemma wf_main : forall (x : type InK),
    isNarrowV narrow (x @% "pkt" @% "op") = false -> wfX F xlen narrow x = wfOf (x @% "pkt").
  Proof.
    intros x Hn.
    pose proof (f_equal (fun o : type (FUOutK F xlen) => (o @% "res") @% "writesF")
                  (fuSpec_main F xlen narrow x Hn)) as E.
    exact (eq_trans E (mainV_writesF _ _ _ _ _ _)).
  Qed.

  (* A narrow conversion writes an f register. *)
  Lemma wf_narrow : forall (x : type InK),
    acceptsF F xlen narrow (cvtFU F xlen narrow) (x @% "pkt") = true -> wfX F xlen narrow x = wfOf (x @% "pkt").
  Proof.
    intros x Hacc.
    unfold wfX, resOf; rewrite (cvtFU_wf F xlen narrow x Hacc).
    unfold acceptsF in Hacc; cbn [fuAccepts cvtFU] in Hacc.
    apply evalExpr_And_true in Hacc; inversion Hacc as [| ? ? Hop _]; subst; clear Hacc.
    rewrite <- isNarrow_pkt in Hop.
    unfold wfOf; rewrite (narrow_not_writesX narrow _ Hop); reflexivity.
  Qed.

  Lemma fpuFUsP_wf : FUsWf F xlen narrow lpsStd.
  Proof.
    intros q Hq x Hacc; unfold fpuFUsP in Hq; apply in_app_or in Hq; destruct Hq as [Hq | Hq].
    - destruct Hq as [<- | [<- | [<- | []]]]; apply wf_main; unfold acceptsF in Hacc;
        cbn [fuL fuAccepts pipeFU divFU sqrtFU] in Hacc.
      + apply evalExpr_And_true in Hacc.
        inversion Hacc as [| ? ? _ Hacc1]; subst; clear Hacc.
        inversion Hacc1 as [| ? ? _ Hacc2]; subst; clear Hacc1.
        inversion Hacc2 as [| ? ? Hn _]; subst; clear Hacc2.
        apply evalExpr_Not_true in Hn; rewrite isNarrow_pkt; exact Hn.
      + apply div_not_narrow; exact Hacc.
      + apply sqrt_not_narrow; exact Hacc.
    - apply In_optTail in Hq; destruct Hq as [<- | []]; apply wf_narrow; exact Hacc.
  Qed.

  Theorem fpu_refines_std : forall env1 env2,
    ModSimulationInit env1 env2 (fpuImplMod F xlen narrow (map (fuL F xlen narrow) lpsStd)) (fpuSpecMod true F xlen narrow)
      (RelFpu F xlen narrow lpsStd) (rel_init F xlen narrow lpsStd (fpuFUsP_ok F xlen narrow ms bps H_cfg)).
  Proof.
    intros env1 env2.
    exact (fpu_refines true F xlen narrow (fun _ _ _ _ _ _ => eq_refl) lpsStd (fpuFUsP_ok F xlen narrow ms bps H_cfg) fpuFUsP_wf env1 env2).
  Qed.
End Standard.
