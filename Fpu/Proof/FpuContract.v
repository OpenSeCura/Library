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
 * The interface contract of the pipelined FPU (`FpuContract.v`), in the sense of Guru's
 * `Interface.v`: what a parent may assume about the FPU when it only calls its methods.
 *
 * Abstract state `FpuAbs`:
 * - `fa_arch` : the architectural state of the atomic spec with every accepted operation
 *   already applied (issued operations still in the pipeline included);
 * - `fa_int`  : the integer result of the accepted integer-result operation, until collected;
 * - `fa_resv` : one bit per f register reserved by a load and not filled yet.  A reserved
 *   register keeps its old value in `fa_arch` until `fpuFill`.
 *
 * `FpuView S a` relates an impl state to its abstract state.  Each method moves the abstract
 * state by its `*Step` relation; a refused call (`ok = false`, `valid = false`) changes
 * nothing; the internal rules do not change it (`fc_rules`).  The contract says nothing about
 * when a call is accepted.
 *
 * `fpu_contract` holds for any fus satisfying `FUOkP` / `FUsWf` and any spec exponent mode
 * agreeing with the biased one; `fpu_contract_ref` is the instance for the standard fus and
 * the spec of record (`bm = false`, the reference core).
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Arith.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas Interface.
From Fpu Require Import FpUtil FpCore FpCoreRef FpuArch SpecFpu FpuFU ImplFpu.
From Fpu Require Import FpuArchLemmas SpecFpuLemmas FpuFUProof BitVecLemmas ImplFpuLemmas RelFpu
  FpCoreRefProof SpecFpuRef.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Open Scope list_scope.

Lemma app_cons_unit : forall {T : Type} (l1 l2 : list T) (a b : T),
  l1 ++ a :: l2 = [b] -> l1 = [] /\ a = b /\ l2 = [].
Proof.
  intros T l1 l2 a b H; destruct l1 as [| c l1]; cbn in H.
  - injection H as -> ->; auto.
  - injection H as _ H; destruct l1; discriminate H.
Qed.

Section FpuContract.
  Variable bm : bool.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.
  Hypothesis H_bm : forall pkt rm a b c x,
    execResOf bm F xlen wlen narrow pkt rm a b c x = execResOf true F xlen wlen narrow pkt rm a b c x.

  Variable lps : list (FUP F xlen narrow).
  Hypothesis H_fus : Forall (FUOkP F xlen wlen narrow) lps.
  Hypothesis H_wf : FUsWf F xlen wlen narrow lps.

  Local Abbreviation fus := (map (fuL F xlen narrow) lps).
  Local Abbreviation IT := (implTree F xlen narrow fus).
  Local Abbreviation ImplSt := (TreeState ElemState IT).
  Local Abbreviation St := (ArchSt flen).
  Local Abbreviation ST := (fpuArchTree flen).
  Local Abbreviation PktK := (FpuPktK narrow).
  Local Abbreviation EntryT := (Entry F xlen narrow).
  Local Abbreviation fS := (foldSem F xlen wlen narrow).
  Local Abbreviation isPI := (isPendInt F xlen wlen narrow).
  Local Abbreviation RELC := (RelC F xlen wlen narrow lps).
  Local Abbreviation mkS := (mkIT F xlen narrow fus).
  Local Abbreviation EX := (EExec F xlen narrow).
  Local Abbreviation EL := (ELoad F xlen narrow).
  Local Abbreviation xresOf x := ((resOf F xlen wlen narrow x) @% "xres").

  (* ===========================================================================
   * 1. ABSTRACT STATE, VIEW, STEPS
   * =========================================================================== *)

  Record FpuAbs := mkAbs {
    fa_arch : St ;
    fa_int  : option (bits xlen) ;
    fa_resv : bits RegVecSz
  }.

  (* The integer result owed to the parent is that of the one pending integer-result entry. *)
  Definition IntOk (g : list EntryT) (o : option (bits xlen)) : Prop :=
    match o with
    | None => filter isPI g = []
    | Some v => exists x i, filter isPI g = [EX x i false] /\ xresOf x = v
    end.

  Definition FpuView (S : ImplSt) (a : FpuAbs) : Prop :=
    exists g sigma A p lp ib Ls,
      S = mkS A (mkCtl p lp ib) Ls /\ RELC g A p lp ib Ls sigma /\
      fa_arch a = fS g sigma /\ IntOk g (fa_int a) /\ fa_resv a = lp.

  Local Abbreviation resvd a r := (bitOf (fa_resv a) r).

  (* An accepted issue runs the whole operation: sources and destination are not reserved, and
   * no other integer result is owed. *)
  Definition IssueStep (pkt : type PktK) (x : bits xlen) (a : FpuAbs) (ok : type Bool) (a' : FpuAbs) : Prop :=
    if ok then
      resvd a (pktRs1 pkt) = false /\ resvd a (pktRs2 pkt) = false /\ resvd a (pktRs3 pkt) = false /\
      (if wfOf pkt then resvd a (pktRd pkt) = false else fa_int a = None) /\
      a' = mkAbs (execSem bm F xlen wlen narrow (fa_arch a) pkt x)
                 (if wfOf pkt then fa_int a
                  else Some ((execRes bm F xlen wlen narrow (fa_arch a) pkt x) @% "xres"))
                 (fa_resv a)
    else a' = a.

  Definition IntRespStep (a : FpuAbs) (r : type (Option (Bit xlen))) (a' : FpuAbs) : Prop :=
    if r @% "valid" then fa_int a = Some (r @% "data") /\ a' = mkAbs (fa_arch a) None (fa_resv a)
    else a' = a.

  Definition ReserveStep (rd : bits FprIdxSz) (a : FpuAbs) (ok : type Bool) (a' : FpuAbs) : Prop :=
    if ok then
      resvd a rd = false /\
      a' = mkAbs (archSetFs flen (fa_arch a) dirtyZ) (fa_int a) (bitSetV (fa_resv a) rd)
    else a' = a.

  Definition FillStep (rd : bits FprIdxSz) (v : bits flen) (a : FpuAbs) (ok : type Bool) (a' : FpuAbs) : Prop :=
    ok = resvd a rd /\
    a' = (if ok then mkAbs (archSetFpr flen (fa_arch a) rd v) (fa_int a) (bitClrV (fa_resv a) rd) else a).

  Definition ReadStep (idx : bits FprIdxSz) (a : FpuAbs) (r : type (Option (Bit flen))) (a' : FpuAbs) : Prop :=
    a' = a /\ (r @% "valid" = true -> resvd a idx = false /\ r @% "data" = archFpr flen (fa_arch a) idx).

  Definition WriteStep (idx : bits FprIdxSz) (v : bits flen) (a : FpuAbs) (ok : type Bool) (a' : FpuAbs) : Prop :=
    if ok then
      resvd a idx = false /\ a' = mkAbs (writeSem F (fa_arch a) idx v) (fa_int a) (fa_resv a)
    else a' = a.

  Definition FflagsReadStep (a : FpuAbs) (r : type (Option (Bit 5))) (a' : FpuAbs) : Prop :=
    a' = a /\ (r @% "valid" = true -> r @% "data" = archFflags flen (fa_arch a)).

  Definition FcsrReadStep (a : FpuAbs) (r : type (Option (Bit 8))) (a' : FpuAbs) : Prop :=
    a' = a /\ (r @% "valid" = true -> r @% "data" = fcsrOf F (fa_arch a)).

  Definition FflagsWriteStep (v : bits 5) (a : FpuAbs) (ok : type Bool) (a' : FpuAbs) : Prop :=
    if ok then fa_int a = None /\ a' = mkAbs (fflagsWriteSem F (fa_arch a) v) (fa_int a) (fa_resv a)
    else a' = a.

  Definition FcsrWriteStep (v : bits 8) (a : FpuAbs) (ok : type Bool) (a' : FpuAbs) : Prop :=
    if ok then fa_int a = None /\ a' = mkAbs (fcsrWriteSem F (fa_arch a) v) (fa_int a) (fa_resv a)
    else a' = a.

  Definition FrmReadStep (a : FpuAbs) (r : type (Bit 3)) (a' : FpuAbs) : Prop :=
    a' = a /\ r = archFrm flen (fa_arch a).

  Definition FrmWriteStep (v : bits 3) (a : FpuAbs) (_ : type (Bit 0)) (a' : FpuAbs) : Prop :=
    a' = mkAbs (frmWriteSem F (fa_arch a) v) (fa_int a) (fa_resv a).

  Definition FsReadStep (a : FpuAbs) (r : type (Bit 2)) (a' : FpuAbs) : Prop :=
    a' = a /\ r = archFs flen (fa_arch a).

  Definition FsWriteStep (v : bits 2) (a : FpuAbs) (_ : type (Bit 0)) (a' : FpuAbs) : Prop :=
    a' = mkAbs (fsWriteSem F (fa_arch a) v) (fa_int a) (fa_resv a).

  (* ===========================================================================
   * 2. GHOST-LIST FACTS
   * =========================================================================== *)

  Lemma view_intro : forall g sigma A p lp ib Ls arch o,
    RELC g A p lp ib Ls sigma -> arch = fS g sigma -> IntOk g o ->
    FpuView (mkS A (mkCtl p lp ib) Ls) (mkAbs arch o lp).
  Proof.
    intros g sigma A p lp ib Ls arch o H Ha Hi.
    exists g, sigma, A, p, lp, ib, Ls; split; [reflexivity | split; [exact H | split; [exact Ha | split; [exact Hi | reflexivity]]]].
  Qed.

  Lemma IntOk_ext : forall g g' o, filter isPI g = filter isPI g' -> IntOk g o -> IntOk g' o.
  Proof. intros g g' o E H; unfold IntOk in *; rewrite <- E; exact H. Qed.

  Lemma IntOk_snoc : forall g e o, isPI e = false -> IntOk g o -> IntOk (g ++ [e]) o.
  Proof.
    intros g e o He H; apply (IntOk_ext g); [| exact H].
    rewrite filter_app; cbn [filter]; rewrite He, app_nil_r; reflexivity.
  Qed.

  Lemma IntOk_nil : forall g o, filter isPI g = [] -> IntOk g o -> o = None.
  Proof.
    intros g [v |] E H; [| reflexivity].
    destruct H as [x [i [Hf _]]]; rewrite E in Hf; discriminate Hf.
  Qed.

  Lemma IntOk_idle : forall g A p lp Ls sigma o, RELC g A p lp false Ls sigma -> IntOk g o -> o = None.
  Proof.
    intros g A p lp Ls sigma o H Hi; apply (IntOk_nil g); [| exact Hi].
    apply length_zero_iff_nil; exact (r_ib _ _ _ _ _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma busy_lp : forall p lp r, busyF p lp r = false -> bitOf lp r = false.
  Proof. intros p lp r H; unfold busyF in H; apply orb_false_iff in H; exact (proj2 H). Qed.

  Lemma drained_ib : forall p ib, drainedF p ib = true -> ib = false.
  Proof. intros p ib H; unfold drainedF in H; apply andb_true_iff in H; destruct H as [_ H]; apply negb_true_iff in H; exact H. Qed.

  (* An exec entry replays as the spec's `execSem`. *)
  Lemma execSem_entry : forall (s : St) pkt xv i d,
    execSem bm F xlen wlen narrow s pkt xv = entrySem F xlen wlen narrow (EExec F xlen narrow (inpOf F xlen narrow s pkt xv) i d) s.
  Proof. intros; unfold execSem, execRes; rewrite H_bm; exact eq_refl. Qed.

  (* The done flag of an entry does not matter for the replayed state. *)
  Lemma fold_done : forall pre x i d post s, fS (pre ++ EX x i d :: post) s = fS (pre ++ EX x i true :: post) s.
  Proof. intros; rewrite !foldSem_app; reflexivity. Qed.

  Lemma isPI_wf : forall x i, wfX F xlen wlen narrow x = true -> isPI (EX x i false) = false.
  Proof. intros x i Hw; cbn [isPendInt]; rewrite Hw; reflexivity. Qed.

  Lemma isPI_int : forall x i, wfX F xlen wlen narrow x = false -> isPI (EX x i false) = true.
  Proof. intros x i Hw; cbn [isPendInt]; rewrite Hw; reflexivity. Qed.

  Lemma filter_done_wf : forall pre x i post, wfX F xlen wlen narrow x = true ->
    filter isPI (pre ++ EX x i false :: post) = filter isPI (pre ++ EX x i true :: post).
  Proof. intros pre x i post Hw; rewrite !filter_app; cbn [filter]; rewrite (isPI_wf x i Hw); reflexivity. Qed.

  (* A write of `rd` commutes with an entry that does not write `rd`. *)
  Lemma entrySem_setFpr : forall e s rd v, writesR F xlen wlen narrow e rd = false ->
    entrySem F xlen wlen narrow e (archSetFpr flen s rd v) = archSetFpr flen (entrySem F xlen wlen narrow e s) rd v.
  Proof.
    intros e s rd v Hw; destruct e as [x i d | r [w |] | r w | w | w | w | w]; cbn [entrySem writesR] in *.
    - unfold applyRes; fold (wfX F xlen wlen narrow x) in *.
      change ((resOf F xlen wlen narrow x) @% "writesF") with (wfX F xlen wlen narrow x).
      destruct (wfX F xlen wlen narrow x); cbn [andb] in Hw; [| reflexivity].
      rewrite (archSetFpr_comm flen s rd (rdOf F xlen narrow x)); [reflexivity |].
      intros E; rewrite E, Zmod.eqb_refl in Hw; discriminate Hw.
    - unfold writeSem; rewrite (archSetFpr_comm flen s rd r); [reflexivity |].
      intros E; rewrite E, Zmod.eqb_refl in Hw; discriminate Hw.
    - reflexivity.
    - unfold writeSem; rewrite (archSetFpr_comm flen s rd r); [reflexivity |].
      intros E; rewrite E, Zmod.eqb_refl in Hw; discriminate Hw.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma fold_setFpr : forall l s rd v, (forall e, In e l -> writesR F xlen wlen narrow e rd = false) ->
    fS l (archSetFpr flen s rd v) = archSetFpr flen (fS l s) rd v.
  Proof.
    induction l as [| e l IH]; intros s rd v Hl; [reflexivity |].
    change (fS l (entrySem F xlen wlen narrow e (archSetFpr flen s rd v)) =
            archSetFpr flen (fS l (entrySem F xlen wlen narrow e s)) rd v).
    rewrite (entrySem_setFpr e s rd v (Hl e (or_introl eq_refl))).
    apply IH; intros e' He'; exact (Hl e' (or_intror He')).
  Qed.

  (* Filling a reserved register writes it in the replayed state: nothing after the reservation
   * touches the register. *)
  Lemma fold_fill : forall pre post rd v s, cleanFor F xlen wlen narrow rd post ->
    fS (pre ++ EL rd (Some v) :: post) s = archSetFpr flen (fS (pre ++ EL rd None :: post) s) rd v.
  Proof.
    intros pre post rd v s Hc; rewrite !foldSem_app.
    set (tp := fS pre s).
    change (fS post (archSetFpr flen (archSetFs flen tp dirtyZ) rd v) =
            archSetFpr flen (fS post (archSetFs flen tp dirtyZ)) rd v).
    apply fold_setFpr; intros e He; exact (proj1 (Hc e He)).
  Qed.

  (* ===========================================================================
   * 3. THE METHODS
   * =========================================================================== *)

  Local Abbreviation EOK := (fun _ : Env IT => True).
  Local Abbreviation MOK := (MethodOk EOK FpuView).

  Ltac open_view a Hv :=
    let arch := fresh "arch" in let int := fresh "int" in let resv := fresh "resv" in
    destruct a as [arch int resv];
    destruct Hv as [g [sigma [A [p [lp [ib [Ls [-> [H [Ha [Hi Hr]]]]]]]]]]];
    cbn [fa_arch fa_int fa_resv] in Ha, Hi, Hr; subst arch resv.

  Lemma issue_ok : forall pkt xv, MOK (fpuIssue F xlen narrow fus type pkt xv) (IssueStep pkt xv).
  Proof.
    intros pkt xv env S S' ok a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuIssue_fwd F xlen wlen narrow lps env A p lp ib Ls pkt xv _ _ H_fus (r_fus _ _ _ _ _ _ _ _ _ _ _ _ H) Hev)
      as [S2 [ok2 [[-> ->] [Hf Ht]]]].
    unfold IssueStep; cbn [fa_arch fa_int fa_resv]; destruct ok.
    - destruct (Ht eq_refl) as [Hsb [i [Ls' [Hrt [Hl ->]]]]].
      destruct (sbOkF_true _ _ _ _ _ _ Hsb) as [Hb1 [Hb2 [Hb3 Hb4]]].
      assert (Hx : inpOf F xlen narrow A pkt xv = inpOf F xlen narrow (fS g sigma) pkt xv).
      { unfold inpOf.
        rewrite (r_frm _ _ _ _ _ _ _ _ _ _ _ _ H), (r_fpr _ _ _ _ _ _ _ _ _ _ _ _ H _ Hb1),
          (r_fpr _ _ _ _ _ _ _ _ _ _ _ _ H _ Hb2), (r_fpr _ _ _ _ _ _ _ _ _ _ _ _ H _ Hb3).
        reflexivity. }
      pose proof (relC_issue F xlen wlen narrow lps g A p lp ib Ls sigma pkt xv i Ls' H_wf H Hsb Hrt Hl) as H'.
      rewrite Hx in H'.
      pose proof (route_wf F xlen wlen narrow lps H_wf (inpOf F xlen narrow (fS g sigma) pkt xv) i) as Hw.
      rewrite inpOf_pkt in Hw; specialize (Hw Hrt).
      assert (Harch : execSem bm F xlen wlen narrow (fS g sigma) pkt xv =
                      fS (g ++ [EX (inpOf F xlen narrow (fS g sigma) pkt xv) i false]) sigma).
      { rewrite foldSem_snoc; exact (execSem_entry (fS g sigma) pkt xv i false). }
      assert (Hxres : (execRes bm F xlen wlen narrow (fS g sigma) pkt xv) @% "xres" =
                      xresOf (inpOf F xlen narrow (fS g sigma) pkt xv)).
      { unfold execRes; rewrite H_bm; exact eq_refl. }
      destruct (wfOf pkt) eqn:Ew.
      + eexists; split; [split; [exact (busy_lp _ _ _ Hb1) | split; [exact (busy_lp _ _ _ Hb2) |
          split; [exact (busy_lp _ _ _ Hb3) | split; [exact (busy_lp _ _ _ Hb4) | reflexivity]]]] |].
        apply (view_intro _ _ _ _ _ _ _ _ _ H' Harch).
        apply IntOk_snoc; [apply isPI_wf; exact Hw | exact Hi].
      + subst ib; pose proof (IntOk_idle _ _ _ _ _ _ _ H Hi) as ->.
        eexists; split; [split; [exact (busy_lp _ _ _ Hb1) | split; [exact (busy_lp _ _ _ Hb2) |
          split; [exact (busy_lp _ _ _ Hb3) | split; [reflexivity | reflexivity]]]] |].
        apply (view_intro _ _ _ _ _ _ _ _ _ H' Harch).
        unfold IntOk in Hi |- *; eexists _, i; split; [| symmetry; exact Hxres].
        rewrite filter_app, Hi; cbn [filter app]; rewrite (isPI_int _ i Hw); reflexivity.
    - rewrite (Hf eq_refl); eexists; split; [reflexivity |].
      exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma intResp_ok : MOK (fpuIntResp F xlen narrow fus type) IntRespStep.
  Proof.
    intros env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuIntResp_fwd F xlen wlen narrow lps env A p lp ib Ls _ _ H_fus (r_fus _ _ _ _ _ _ _ _ _ _ _ _ H) Hev)
      as [S2 [r2 [[-> ->] [Hf Ht]]]].
    unfold IntRespStep; cbn [fa_arch fa_int fa_resv]; destruct (r @% "valid") eqn:Hval.
    - destruct (Ht eq_refl) as [i [x [rest [Ls' [Hx [Hw [Hd [Hl ->]]]]]]]].
      destruct (relC_intResp F xlen wlen narrow lps g A p lp ib Ls sigma i x rest Ls' H Hx Hw Hl) as [pre [post [Hg H']]].
      subst g.
      assert (Hfil : filter isPI (pre ++ EX x i false :: post) = filter isPI pre ++ EX x i false :: filter isPI post).
      { rewrite filter_app; cbn [filter]; rewrite (isPI_int x i Hw); reflexivity. }
      assert (Hint : int = Some (r @% "data") /\ filter isPI pre = [] /\ filter isPI post = []).
      { destruct int as [v |]; unfold IntOk in Hi.
        - destruct Hi as [x0 [i0 [Hf0 Hv0]]]; rewrite Hfil in Hf0.
          destruct (app_cons_unit _ _ _ _ Hf0) as [Hp [He Hq]].
          split; [| exact (conj Hp Hq)].
          assert (Ex : x = x0) by (injection He as Ex _; exact Ex).
          rewrite <- Hv0, <- Ex, Hd; reflexivity.
        - rewrite Hfil in Hi; destruct (filter isPI pre); discriminate Hi. }
      destruct Hint as [-> [Hp Hq]].
      eexists; split; [split; reflexivity |].
      apply (view_intro _ _ _ _ _ _ _ _ _ H' (fold_done pre x i false post sigma)).
      unfold IntOk; rewrite filter_app; cbn [filter isPendInt]; rewrite Hp, Hq; reflexivity.
    - rewrite (Hf eq_refl); eexists; split; [reflexivity |].
      exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma reserve_ok : forall rd, MOK (fpuReserve F xlen narrow fus type rd) (ReserveStep rd).
  Proof.
    intros rd env S S' ok a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuReserve_fwd F xlen narrow lps env A p lp ib Ls rd _ Hev) as [S2 [ok2 [[-> ->] [Hok ->]]]].
    unfold ReserveStep; cbn [fa_arch fa_int fa_resv]; destruct ok.
    - symmetry in Hok; apply negb_true_iff in Hok.
      eexists; split; [split; [exact (busy_lp _ _ _ Hok) | reflexivity] |].
      apply (view_intro _ _ _ _ _ _ _ _ _ (relC_reserve F xlen wlen narrow lps g A p lp ib Ls sigma rd H Hok)).
      + rewrite foldSem_snoc; reflexivity.
      + apply IntOk_snoc; [reflexivity | exact Hi].
    - eexists; split; [reflexivity |]; exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma fill_ok : forall rd v, MOK (fpuFill F xlen narrow fus type rd v) (FillStep rd v).
  Proof.
    intros rd v env S S' ok a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuFill_fwd F xlen narrow lps env A p lp ib Ls rd v _ Hev) as [S2 [ok2 [[-> ->] [Hok ->]]]].
    unfold FillStep; cbn [fa_arch fa_int fa_resv]; destruct ok.
    - destruct (relC_fill F xlen wlen narrow lps g A p lp ib Ls sigma rd v H (eq_sym Hok)) as [pre [post [Hg H']]].
      subst g.
      assert (Hc : cleanFor F xlen wlen narrow rd post).
      { pose proof (r_nlt _ _ _ _ _ _ _ _ _ _ _ _ H) as Hn; apply NLT_app in Hn; destruct Hn as [_ [[Hc _] _]].
        apply Hc; unfold pendW; cbn [pendWE pendWL]; apply Zmod.eqb_refl. }
      eexists; split; [split; [exact Hok | reflexivity] |].
      apply (view_intro _ _ _ _ _ _ _ _ _ H').
      + symmetry; exact (fold_fill pre post rd v sigma Hc).
      + apply (IntOk_ext (pre ++ EL rd None :: post)); [rewrite !filter_app; reflexivity | exact Hi].
    - eexists; split; [split; [exact Hok | reflexivity] |]; exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma readT_ok : forall idx, MOK (fpuReadT F xlen narrow fus type idx) (ReadStep idx).
  Proof.
    intros idx env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuReadT_fwd F xlen narrow lps env A p lp ib Ls idx _ Hev) as [r2 [[<- ->] [Hd Hv2]]].
    eexists; split; [| exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi)].
    split; [reflexivity |]; cbn [fa_arch fa_resv]; intros Hval.
    rewrite Hval in Hv2; symmetry in Hv2; apply negb_true_iff in Hv2.
    split; [exact (busy_lp _ _ _ Hv2) | rewrite Hd; exact (r_fpr _ _ _ _ _ _ _ _ _ _ _ _ H _ Hv2)].
  Qed.

  Lemma writeT_ok : forall idx v, MOK (fpuWriteT F xlen narrow fus type idx v) (WriteStep idx v).
  Proof.
    intros idx v env S S' ok a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuWriteT_fwd F xlen narrow lps env A p lp ib Ls idx v _ Hev) as [S2 [ok2 [[-> ->] [Hok ->]]]].
    unfold WriteStep; cbn [fa_arch fa_int fa_resv]; destruct ok.
    - symmetry in Hok; apply negb_true_iff in Hok.
      eexists; split; [split; [exact (busy_lp _ _ _ Hok) | reflexivity] |].
      apply (view_intro _ _ _ _ _ _ _ _ _ (relC_writeT F xlen wlen narrow lps g A p lp ib Ls sigma idx v H Hok)).
      + rewrite foldSem_snoc; reflexivity.
      + apply IntOk_snoc; [reflexivity | exact Hi].
    - eexists; split; [reflexivity |]; exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma fflagsReadT_ok : MOK (fpuFflagsReadT F xlen narrow fus type) FflagsReadStep.
  Proof.
    intros env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    apply fpuFflagsReadT_fwd in Hev; destruct Hev as [<- <-].
    eexists; split; [| exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi)].
    split; [reflexivity |]; cbn [fa_arch]; intros Hd.
    rewrite (r_ff _ _ _ _ _ _ _ _ _ _ _ _ H), (drained_pendFlags _ _ _ _ _ _ _ _ _ _ _ _ H Hd), bits_or_0_r; reflexivity.
  Qed.

  Lemma fcsrReadT_ok : MOK (fpuFcsrReadT F xlen narrow fus type) FcsrReadStep.
  Proof.
    intros env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    apply fpuFcsrReadT_fwd in Hev; destruct Hev as [<- <-].
    eexists; split; [| exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi)].
    split; [reflexivity |]; cbn [fa_arch]; intros Hd.
    unfold fcsrOf; rewrite <- (r_frm _ _ _ _ _ _ _ _ _ _ _ _ H), (r_ff _ _ _ _ _ _ _ _ _ _ _ _ H),
      (drained_pendFlags _ _ _ _ _ _ _ _ _ _ _ _ H Hd), bits_or_0_r; reflexivity.
  Qed.

  Lemma fflagsWriteT_ok : forall v, MOK (fpuFflagsWriteT F xlen narrow fus type v) (FflagsWriteStep v).
  Proof.
    intros v env S S' ok a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuFflagsWriteT_fwd F xlen narrow lps env A p lp ib Ls v _ Hev) as [S2 [ok2 [[-> ->] [Hok ->]]]].
    unfold FflagsWriteStep; cbn [fa_arch fa_int fa_resv]; destruct ok.
    - symmetry in Hok; pose proof (drained_ib _ _ Hok) as Eib; subst ib.
      eexists; split; [split; [exact (IntOk_idle _ _ _ _ _ _ _ H Hi) | reflexivity] |].
      apply (view_intro _ _ _ _ _ _ _ _ _ (relC_fflags F xlen wlen narrow lps g A p lp false Ls sigma v H Hok)).
      + rewrite foldSem_snoc; reflexivity.
      + apply IntOk_snoc; [reflexivity | exact Hi].
    - eexists; split; [reflexivity |]; exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma fcsrWriteT_ok : forall v, MOK (fpuFcsrWriteT F xlen narrow fus type v) (FcsrWriteStep v).
  Proof.
    intros v env S S' ok a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (fpuFcsrWriteT_fwd F xlen narrow lps env A p lp ib Ls v _ Hev) as [S2 [ok2 [[-> ->] [Hok ->]]]].
    unfold FcsrWriteStep; cbn [fa_arch fa_int fa_resv]; destruct ok.
    - symmetry in Hok; pose proof (drained_ib _ _ Hok) as Eib; subst ib.
      eexists; split; [split; [exact (IntOk_idle _ _ _ _ _ _ _ H Hi) | reflexivity] |].
      apply (view_intro _ _ _ _ _ _ _ _ _ (relC_fcsr F xlen wlen narrow lps g A p lp false Ls sigma v H Hok)).
      + rewrite foldSem_snoc; reflexivity.
      + apply IntOk_snoc; [reflexivity | exact Hi].
    - eexists; split; [reflexivity |]; exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi).
  Qed.

  Lemma frmRead_ok : MOK (fpuFrmRead F xlen narrow fus type) FrmReadStep.
  Proof.
    intros env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    apply ev_fpuFrmRead in Hev; destruct Hev as [<- <-].
    eexists; split; [| exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi)].
    split; [reflexivity | exact (r_frm _ _ _ _ _ _ _ _ _ _ _ _ H)].
  Qed.

  Lemma frmWrite_ok : forall v, MOK (fpuFrmWrite F xlen narrow fus type v) (FrmWriteStep v).
  Proof.
    intros v env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    apply ev_fpuFrmWrite in Hev; destruct Hev as [<- _].
    eexists; split; [reflexivity |].
    apply (view_intro _ _ _ _ _ _ _ _ _ (relC_frm F xlen wlen narrow lps g A p lp ib Ls sigma v H)).
    - rewrite foldSem_snoc; reflexivity.
    - apply IntOk_snoc; [reflexivity | exact Hi].
  Qed.

  Lemma fsRead_ok : MOK (fpuFsRead F xlen narrow fus type) FsReadStep.
  Proof.
    intros env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    apply ev_fpuFsRead in Hev; destruct Hev as [<- <-].
    eexists; split; [| exact (view_intro _ _ _ _ _ _ _ _ _ H eq_refl Hi)].
    split; [reflexivity | exact (r_fs _ _ _ _ _ _ _ _ _ _ _ _ H)].
  Qed.

  Lemma fsWrite_ok : forall v, MOK (fpuFsWrite F xlen narrow fus type v) (FsWriteStep v).
  Proof.
    intros v env S S' r a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    apply ev_fpuFsWrite in Hev; destruct Hev as [<- _].
    eexists; split; [reflexivity |].
    apply (view_intro _ _ _ _ _ _ _ _ _ (relC_fs F xlen wlen narrow lps g A p lp ib Ls sigma v H)).
    - rewrite foldSem_snoc; reflexivity.
    - apply IntOk_snoc; [reflexivity | exact Hi].
  Qed.

  (* ===========================================================================
   * 4. THE INTERNAL RULES, INITIAL STATES
   * =========================================================================== *)

  (* Pipeline steps and write-backs do not change the abstract state. *)
  Lemma rules_ok : RulesStutter EOK FpuView (fpuImplRules F xlen narrow fus type).
  Proof.
    intros r Hin env S S' z a _ Hv Hsem; open_view a Hv.
    pose proof (InversionActionPropGen Hsem) as Hev; clear Hsem.
    destruct (implRules_fwd F xlen wlen narrow lps H_fus env r (mkS A (mkCtl p lp ib) Ls) (pendIn F xlen narrow g) _
                (r_fus _ _ _ _ _ _ _ _ _ _ _ _ H) Hin Hev)
      as [S2 [HQ Hcase]].
    destruct HQ as [-> _].
    destruct Hcase as [[t' [-> Ht]] | [o [i [x [xs [t' [Hx [Hd [Hw [-> Ht]]]]]]]]]].
    - eexists; split; [reflexivity |].
      exact (view_intro _ _ _ _ _ _ _ _ _ (relC_fus F xlen wlen narrow lps g A p lp ib Ls t' sigma H Ht) eq_refl Hi).
    - destruct (relC_wb F xlen wlen narrow lps g A p lp ib Ls sigma i x xs t' H Hx Hw Ht) as [pre [post [Hg H']]].
      subst g; eexists; split; [reflexivity |].
      rewrite (wbUpdO_eq F xlen wlen narrow lps A p lp ib Ls o x Hd).
      apply (view_intro _ _ _ _ _ _ _ _ _ H' (fold_done pre x i false post sigma)).
      apply (IntOk_ext (pre ++ EX x i false :: post)); [exact (filter_done_wf pre x i post Hw) | exact Hi].
  Qed.

  Lemma fus_init : forall l (Ls : TreeState ElemState (fusTree F xlen narrow (map (fuL F xlen narrow) l))),
    Forall (FUOkP F xlen wlen narrow) l ->
    InitStateConsistent (fusTree F xlen narrow (map (fuL F xlen narrow) l)) Ls ->
    FUsHold F xlen narrow l Ls (fun _ => []).
  Proof.
    induction l as [| q l IH]; intros Ls Hok Hi; [exact I |].
    apply Forall_cons_iff in Hok; destruct Hok as [Hq Hl].
    destruct Ls as [sq [sl []]]; cbn [map fusTree InitStateConsistent] in Hi; destruct Hi as [Hiq [Hil _]].
    split; [exact (lo_init _ _ _ _ _ _ Hq sq Hiq) | exact (IH sl Hl Hil)].
  Qed.

  Lemma arch_init_det : allTreeInitDet ST = true.
  Proof. reflexivity. Qed.

  (* Every initial state stands for the spec's initial state, with nothing owed or reserved. *)
  Lemma init_ok : forall sigma0 : St, InitStateConsistent ST sigma0 ->
    InitOk FpuView (mkAbs sigma0 None Zmod.zero).
  Proof.
    intros sigma0 Hs [A [[p [lp [ib []]]] [Ls []]]] HS.
    cbn [implTree InitStateConsistent] in HS; destruct HS as [HA [[Hp [Hlp [Hib _]]] [HL _]]].
    cbn in Hp, Hlp, Hib; subst p lp ib.
    pose proof (allTreeInitDet_InitStateConsistent_eq ST A sigma0 arch_init_det HA Hs) as ->.
    apply (view_intro [] sigma0); [| reflexivity | reflexivity].
    constructor; try reflexivity; try exact I; try (intros r; apply bitOf_zero); try (intros x i d []);
      try exact (fus_init lps Ls H_fus HL).
    cbn [foldSem fold_left pendFlags fold_right]; rewrite bits_or_0_r; reflexivity.
  Qed.

  (* ===========================================================================
   * 5. THE CONTRACT
   * =========================================================================== *)

  Record FpuContract : Prop := {
    fc_issue        : forall pkt x, MOK (fpuIssue F xlen narrow fus type pkt x) (IssueStep pkt x) ;
    fc_intResp      : MOK (fpuIntResp F xlen narrow fus type) IntRespStep ;
    fc_reserve      : forall rd, MOK (fpuReserve F xlen narrow fus type rd) (ReserveStep rd) ;
    fc_fill         : forall rd v, MOK (fpuFill F xlen narrow fus type rd v) (FillStep rd v) ;
    fc_readT        : forall idx, MOK (fpuReadT F xlen narrow fus type idx) (ReadStep idx) ;
    fc_writeT       : forall idx v, MOK (fpuWriteT F xlen narrow fus type idx v) (WriteStep idx v) ;
    fc_fflagsReadT  : MOK (fpuFflagsReadT F xlen narrow fus type) FflagsReadStep ;
    fc_fcsrReadT    : MOK (fpuFcsrReadT F xlen narrow fus type) FcsrReadStep ;
    fc_fflagsWriteT : forall v, MOK (fpuFflagsWriteT F xlen narrow fus type v) (FflagsWriteStep v) ;
    fc_fcsrWriteT   : forall v, MOK (fpuFcsrWriteT F xlen narrow fus type v) (FcsrWriteStep v) ;
    fc_frmRead      : MOK (fpuFrmRead F xlen narrow fus type) FrmReadStep ;
    fc_frmWrite     : forall v, MOK (fpuFrmWrite F xlen narrow fus type v) (FrmWriteStep v) ;
    fc_fsRead       : MOK (fpuFsRead F xlen narrow fus type) FsReadStep ;
    fc_fsWrite      : forall v, MOK (fpuFsWrite F xlen narrow fus type v) (FsWriteStep v) ;
    fc_rules        : RulesStutter EOK FpuView (fpuImplRules F xlen narrow fus type) ;
    fc_init         : forall sigma0 : St, InitStateConsistent ST sigma0 -> InitOk FpuView (mkAbs sigma0 None Zmod.zero)
  }.

  Theorem fpu_contract : FpuContract.
  Proof.
    constructor.
    - exact issue_ok.
    - exact intResp_ok.
    - exact reserve_ok.
    - exact fill_ok.
    - exact readT_ok.
    - exact writeT_ok.
    - exact fflagsReadT_ok.
    - exact fcsrReadT_ok.
    - exact fflagsWriteT_ok.
    - exact fcsrWriteT_ok.
    - exact frmRead_ok.
    - exact frmWrite_ok.
    - exact fsRead_ok.
    - exact fsWrite_ok.
    - exact rules_ok.
    - exact init_ok.
  Qed.
End FpuContract.

(* ---------------------------------------------------------------------------
 * 6. THE STANDARD FUS SATISFY `FUsWf`
 * --------------------------------------------------------------------------- *)

Section StandardWf.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Variable narrow : list FpFmt.
  Variable ms bps : nat.

  Local Abbreviation InK := (FUInK F xlen narrow).
  Local Abbreviation lpsStd := (fpuFUsP F xlen wlen narrow ms bps).

  Lemma mainV_writesF : forall op rm a b c x,
    (mainV F xlen wlen narrow op rm a b c x) @% "writesF" = negb (opWritesXV narrow op).
  Proof. intros; reflexivity. Qed.

  (* A non-narrow op writes an f register iff it does not write an x register. *)
  Lemma wf_main : forall (x : type InK),
    isNarrowV narrow (x @% "pkt" @% "op") = false -> wfX F xlen wlen narrow x = wfOf (x @% "pkt").
  Proof.
    intros x Hn.
    pose proof (f_equal (fun o : type (FUOutK F xlen) => (o @% "res") @% "writesF")
                  (fuSpec_main F xlen wlen narrow x Hn)) as E.
    exact (eq_trans E (mainV_writesF _ _ _ _ _ _)).
  Qed.

  (* A narrow conversion writes an f register. *)
  Lemma wf_narrow : forall (x : type InK),
    acceptsF F xlen narrow (cvtFU F xlen narrow) (x @% "pkt") = true -> wfX F xlen wlen narrow x = wfOf (x @% "pkt").
  Proof.
    intros x Hacc.
    unfold wfX, resOf; rewrite (cvtFU_wf F xlen wlen narrow x Hacc).
    unfold acceptsF in Hacc; cbn [fuAccepts cvtFU] in Hacc.
    apply evalExpr_And_true in Hacc; inversion Hacc as [| ? ? Hop _]; subst; clear Hacc.
    rewrite <- isNarrow_pkt in Hop.
    unfold wfOf; rewrite (narrow_not_writesX narrow _ Hop); reflexivity.
  Qed.

  Lemma fpuFUsP_wf : FUsWf F xlen wlen narrow lpsStd.
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
End StandardWf.

(* ---------------------------------------------------------------------------
 * 7. THE STANDARD FUS AGAINST THE SPEC OF RECORD
 * --------------------------------------------------------------------------- *)

Section Standard.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Variable narrow : list FpFmt.
  Hypothesis HF : FmtOk F.
  Hypothesis Hx0 : 0 <= xlen.
  Hypothesis Hx1 : xlen + 4 <= 7 * 2 ^ (fmtE F - 1).
  Hypothesis HN : Forall FmtOk narrow.
  Variable ms bps : nat.
  Hypothesis H_cfg : PipeCfgOk F ms bps.

  Theorem fpu_contract_ref :
    FpuContract false F xlen wlen narrow (fpuFUsP F xlen wlen narrow ms bps).
  Proof.
    exact (fpu_contract false F xlen wlen narrow (execResOf_ref F xlen wlen narrow HF Hx0 Hx1 HN)
             (fpuFUsP F xlen wlen narrow ms bps) (fpuFUsP_ok F xlen wlen narrow ms bps H_cfg)
             (fpuFUsP_wf F xlen wlen narrow ms bps)).
  Qed.
End Standard.
