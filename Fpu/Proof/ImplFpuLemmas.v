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
 * Behaviour of the pipelined FPU's actions (`ImplFpuLemmas.v`).
 *
 * The impl state is `(A ,, (C ,, (Ls ,, tt)))`: architectural state `A`, control block
 * `C = (pend ,, (lpend ,, (intBusy ,, tt)))`, fu states `Ls`.  With fus given as `FUP`s
 * (fu + view), `FUsHold lps Ls f` says fu `i` holds `f i`.
 *
 * Forward lemmas (from `evalActionPropGen`, for every environment):
 * - lifting: `ev_liftArch`, `ev_liftCtl`, `ev_liftFUs`;
 * - fu lists: `tryEnqFUs_fwd` (enqueue into the routed fu), `intRespFUs_fwd`;
 * - fu rules: `fusRules_fwd` (each rule is a fu-internal step or a write-back).
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Arith.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Fpu Require Import FpUtil FpCore FpuArch SpecFpu FpuFU ImplFpu.
From Fpu Require Import FpuArchLemmas SpecFpuLemmas FpuFUProof BitVecLemmas.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Open Scope list_scope.

Lemma evalActionPropGen_liftAction_child2Path :
  forall {name c0 c1 c2 cs k} {env : Env (Node name (c0 :: c1 :: c2 :: cs))} (a : @Action type c2 k) sc0 sc1 sc2 scs P,
    evalActionPropGen env (@liftAction type (Node name (c0 :: c1 :: c2 :: cs)) child2Path k a) (sc0 ,, (sc1 ,, (sc2 ,, scs))) P <->
    @evalActionPropGen c2 (subEnv child2Path env (sc0 ,, (sc1 ,, (sc2 ,, scs)))) k a sc2 (fun sc2' r => P (sc0 ,, (sc1 ,, (sc2' ,, scs))) r).
Proof.
  intros name c0 c1 c2 cs k env a sc0 sc1 sc2 scs P.
  exact (evalActionPropGen_liftAction child2Path a (sc0 ,, (sc1 ,, (sc2 ,, scs))) P).
Qed.

(* One-step evaluation of action constructors (head position only). *)
Lemma ev_LetAction : forall {t} (env : Env t) s {k k'} (a : Action type t k') (cont : type k' -> Action type t k) S Q,
  evalActionPropGen env (LetAction s a cont) S Q <-> evalActionPropGen env a S (fun S' r => evalActionPropGen env (cont r) S' Q).
Proof. reflexivity. Qed.

Lemma ev_IfElse_fwd : forall {t} (env : Env t) s (p : Expr type Bool) {k k'} (tb fb : Action type t k')
  (cont : type k' -> Action type t k) S Q,
  evalActionPropGen env (IfElse s p tb fb cont) S Q ->
  (evalExpr p = true /\ evalActionPropGen env tb S (fun S' r => evalActionPropGen env (cont r) S' Q)) \/
  (evalExpr p = false /\ evalActionPropGen env fb S (fun S' r => evalActionPropGen env (cont r) S' Q)).
Proof. intros t env s p k k' tb fb cont S Q H; cbn [evalActionPropGen] in H; destruct (evalExpr p); auto. Qed.

(* ===========================================================================
 * 1. CONTROL BLOCK
 * =========================================================================== *)

Definition CtlSt : Type := TreeState ElemState ctlTree.
Definition mkCtl (p lp : bits RegVecSz) (ib : bool) : CtlSt := (p ,, (lp ,, (ib ,, tt))).

Section CtlLemmas.
  Context {env : Env ctlTree}.
  Variable p lp : bits RegVecSz.
  Variable ib : bool.

  Lemma ev_ctlReadPend : forall P, evalActionPropGen env (ctlReadPend type) (mkCtl p lp ib) P <-> P (mkCtl p lp ib) p.
  Proof. reflexivity. Qed.
  Lemma ev_ctlReadLpend : forall P, evalActionPropGen env (ctlReadLpend type) (mkCtl p lp ib) P <-> P (mkCtl p lp ib) lp.
  Proof. reflexivity. Qed.
  Lemma ev_ctlReadIntBusy : forall P, evalActionPropGen env (ctlReadIntBusy type) (mkCtl p lp ib) P <-> P (mkCtl p lp ib) ib.
  Proof. reflexivity. Qed.
  Lemma ev_ctlWritePend : forall v P, evalActionPropGen env (ctlWritePend type v) (mkCtl p lp ib) P <-> P (mkCtl (evalExpr v) lp ib) Zmod.zero.
  Proof. reflexivity. Qed.
  Lemma ev_ctlWriteLpend : forall v P, evalActionPropGen env (ctlWriteLpend type v) (mkCtl p lp ib) P <-> P (mkCtl p (evalExpr v) ib) Zmod.zero.
  Proof. reflexivity. Qed.
  Lemma ev_ctlWriteIntBusy : forall v P, evalActionPropGen env (ctlWriteIntBusy type v) (mkCtl p lp ib) P <-> P (mkCtl p lp (evalExpr v)) Zmod.zero.
  Proof. reflexivity. Qed.
End CtlLemmas.

(* ===========================================================================
 * 2. LIFTING INTO THE IMPL TREE
 * =========================================================================== *)

Section Lift.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.
  Variable ls : list (FU F xlen narrow).

  Local Abbreviation IT := (implTree F xlen narrow ls).
  Local Abbreviation LsSt := (TreeState ElemState (fusTree F xlen narrow ls)).

  Definition mkIT (A : ArchSt flen) (C : CtlSt) (Ls : LsSt) : TreeState ElemState IT := (A ,, (C ,, (Ls ,, tt))).

  Lemma ev_liftArch : forall {k} (a : Action type (fpuArchTree flen) k) (g : ArchSt flen -> ArchSt flen) (h : ArchSt flen -> type k),
    (forall env' s P, evalActionPropGen env' a s P <-> P (g s) (h s)) ->
    forall (env : Env IT) A C Ls Q,
      evalActionPropGen env (liftArch F xlen narrow ls type a) (mkIT A C Ls) Q <-> Q (mkIT (g A) C Ls) (h A).
  Proof.
    intros k a g h Ha env A C Ls Q; unfold liftArch, mkIT, implTree.
    rewrite evalActionPropGen_liftAction_child0Path, Ha; reflexivity.
  Qed.

  Lemma ev_liftCtl : forall {k} (a : Action type ctlTree k) (g : CtlSt -> CtlSt) (h : CtlSt -> type k) C,
    (forall env' P, evalActionPropGen env' a C P <-> P (g C) (h C)) ->
    forall (env : Env IT) A Ls Q,
      evalActionPropGen env (liftCtl F xlen narrow ls type a) (mkIT A C Ls) Q <-> Q (mkIT A (g C) Ls) (h C).
  Proof.
    intros k a g h C Ha env A Ls Q; unfold liftCtl, mkIT, implTree.
    rewrite evalActionPropGen_liftAction_child1Path, Ha; reflexivity.
  Qed.

  Lemma ev_liftFUs : forall {k} (a : Action type (fusTree F xlen narrow ls) k) (env : Env IT) A C Ls Q,
    evalActionPropGen env (liftFUs F xlen narrow ls type a) (mkIT A C Ls) Q ->
    exists env', evalActionPropGen env' a Ls (fun Ls' r => Q (mkIT A C Ls') r).
  Proof.
    intros k a env A C Ls Q H; unfold liftFUs, mkIT, implTree in *.
    rewrite evalActionPropGen_liftAction_child2Path in H; eexists; exact H.
  Qed.
End Lift.

(* Arch-action lemmas as `(g, h)` pairs for `ev_liftArch`. *)
Section ArchPairs.
  Variable flen : Z.
  Lemma evp_archReadFpr : forall idx env' (s : ArchSt flen) P,
    evalActionPropGen env' (archReadFpr flen type idx) s P <-> P s (archFpr flen s (evalExpr idx)).
  Proof. intros; apply evalActionPropGen_archReadFpr. Qed.
End ArchPairs.

(* ===========================================================================
 * 3. LANE LISTS
 * =========================================================================== *)

Section FUs.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.

  Local Abbreviation FUP := (FUP F xlen narrow).
  Local Abbreviation InK := (FUInK F xlen narrow).
  Local Abbreviation fuL := (fuL F xlen narrow).
  Local Abbreviation fuV := (fuV F xlen narrow).

  Definition FUOkP (p : FUP) : Prop := FUOk F xlen wlen narrow (fuL p) (fuV p).

  Fixpoint FUsHold (lps : list FUP) :
    TreeState ElemState (fusTree F xlen narrow (map fuL lps)) -> (nat -> list (type InK)) -> Prop :=
    match lps return TreeState ElemState (fusTree F xlen narrow (map fuL lps)) -> (nat -> list (type InK)) -> Prop with
    | nil => fun _ _ => True
    | p :: rest => fun s f =>
        lvHolds F xlen narrow (fuL p) (fuV p) s.(Fst) (f 0%nat) /\ FUsHold rest s.(Snd).(Fst) (fun i => f (S i))
    end.

  Lemma FUsHold_ext : forall lps s f g, (forall i, f i = g i) -> FUsHold lps s f -> FUsHold lps s g.
  Proof.
    induction lps as [| p rest IH]; intros s f g Hfg H; [exact I |].
    destruct H as [H0 H1]; split; [rewrite <- Hfg; exact H0 | apply (IH _ _ _ (fun i => Hfg (S i)) H1)].
  Qed.

  (* The fu a packet is routed to: the first one accepting it. *)
  Fixpoint route (lps : list FUP) (pkt : type (FpuPktK narrow)) : option nat :=
    match lps with
    | nil => None
    | p :: rest => if acceptsF F xlen narrow (fuL p) pkt then Some 0%nat else option_map S (route rest pkt)
    end.

  Definition setAt (f : nat -> list (type InK)) (i : nat) (xs : list (type InK)) : nat -> list (type InK) :=
    fun j => if Nat.eqb j i then xs else f j.

  Lemma setAt_shift : forall f i xs j, setAt f (S i) xs (S j) = setAt (fun k => f (S k)) i xs j.
  Proof. reflexivity. Qed.

  Lemma setAt_0_shift : forall f xs j, setAt f 0 xs (S j) = f (S j).
  Proof. reflexivity. Qed.

  Lemma tryEnqFUs_fwd : forall lps (env : Env (fusTree F xlen narrow (map fuL lps))) s f go pkt (inp : type InK) Q,
    Forall FUOkP lps -> FUsHold lps s f -> inp @% "pkt" = pkt ->
    evalActionPropGen env (tryEnqFUs F xlen narrow type (map fuL lps) go pkt inp) s Q ->
    exists s' (b : bool), Q s' b /\
      (b = false -> s' = s) /\
      (b = true -> go = true /\ exists i, route lps pkt = Some i /\ FUsHold lps s' (setAt f i (f i ++ [inp]))).
  Proof.
    induction lps as [| p rest IH]; intros env s f go pkt inp Q Hok Hh Hpkt H.
    - cbn [tryEnqFUs map evalActionPropGen] in H.
      exists s, false; split; [exact H | split; [reflexivity | discriminate]].
    - apply Forall_cons_iff in Hok; destruct Hok as [Hp Hrest].
      destruct s as [sl [sr []]]; destruct Hh as [Hl Hr].
      cbn [tryEnqFUs map fusTree evalActionPropGen] in H.
      destruct (evalExpr (fuAccepts F xlen narrow (fuL p) type pkt)) eqn:Hacc.
      + rewrite evalActionPropGen_liftAction_child0Path in H.
        destruct (lo_canEnq _ _ _ _ _ _ Hp _ _ _ H) as [b [H1 Hb]].
        cbn [evalActionPropGen] in H1.
        destruct (andb go b) eqn:Hgb; cbn [evalExpr fold_left map evalAndBinary evalBinary KindCustomInd InvDefault andb] in H1;
          rewrite Hgb in H1; cbn [evalActionPropGen] in H1.
        * apply andb_true_iff in Hgb; destruct Hgb as [-> ->].
          rewrite evalActionPropGen_liftAction_child0Path in H1.
          destruct (lo_enq _ _ _ _ _ _ Hp _ _ _ _ _ Hl (Hb eq_refl) ltac:(rewrite Hpkt; exact Hacc) H1) as [sl' [H2 Hl']].
          cbn [evalActionPropGen] in H2.
          eexists _, true; split; [exact H2 | split; [discriminate |]]; intros _; split; [reflexivity |].
          exists 0%nat; split; [cbn [route]; unfold acceptsF; rewrite Hacc; reflexivity |].
          cbn [FUsHold Fst Snd]; split; [exact Hl' |].
          apply (FUsHold_ext _ _ (fun i => f (S i))); [intros i; reflexivity | exact Hr].
        * eexists _, false; split; [exact H1 | split; [reflexivity | discriminate]].
      + rewrite evalActionPropGen_liftAction_child1Path in H.
        destruct (IH _ _ (fun i => f (S i)) go pkt inp _ Hrest Hr Hpkt H) as [sr' [b [H1 [Hf Ht]]]].
        cbn [evalActionPropGen] in H1.
        eexists _, b; split; [exact H1 | split].
        * intros Hb; rewrite (Hf Hb); reflexivity.
        * intros Hb; destruct (Ht Hb) as [Hgo [i [Hi Hs]]]; split; [exact Hgo |].
          exists (S i); split; [cbn [route]; unfold acceptsF; rewrite Hacc, Hi; reflexivity |].
          cbn [FUsHold Fst Snd]; split; [exact Hl |].
          apply (FUsHold_ext _ _ _ _ (fun j => eq_refl) Hs).
  Qed.

  Local Abbreviation OutK := (FUOutK F xlen).
  Local Abbreviation ResK := (FpuResK F xlen).

  Lemma evalExpr_And2 : forall (a b : Expr type Bool), evalExpr (And [a; b]) = andb (evalExpr a) (evalExpr b).
  Proof. intros a b; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b); reflexivity. Qed.

  Lemma evalExpr_And2_Not : forall (a b : Expr type Bool),
    evalExpr (And [ a ; Not b ]) = andb (evalExpr a) (negb (evalExpr b)).
  Proof. intros a b; cbn [evalExpr fold_left map]; destruct (evalExpr a), (evalExpr b); reflexivity. Qed.

  Lemma intRespFUs_fwd : forall lps (env : Env (fusTree F xlen narrow (map fuL lps))) s f Q,
    Forall FUOkP lps -> FUsHold lps s f ->
    evalActionPropGen env (intRespFUs F xlen narrow type (map fuL lps)) s Q ->
    exists s' (r : type (Option ResK)), Q s' r /\
      (r @% "valid" = false -> s' = s) /\
      (r @% "valid" = true -> exists i x rest, f i = x :: rest /\
         r @% "data" = (fuSpec F xlen wlen narrow x) @% "res" /\
         (fuSpec F xlen wlen narrow x) @% "res" @% "writesF" = false /\
         FUsHold lps s' (setAt f i rest)).
  Proof.
    induction lps as [| p rest IH]; intros env s f Q Hok Hh H.
    - cbn [intRespFUs map evalActionPropGen] in H.
      eexists _, _; split; [exact H | split; [reflexivity | intros Hv; discriminate Hv]].
    - apply Forall_cons_iff in Hok; destruct Hok as [Hp Hrest].
      destruct s as [sl [sr []]]; destruct Hh as [Hl Hr].
      cbn [intRespFUs map fusTree] in H; apply ev_LetAction in H.
      rewrite (@evalActionPropGen_liftAction_child0Path "fus" _ [fusTree F xlen narrow (map fuL rest)] _ env) in H.
      destruct (lo_first _ _ _ _ _ _ Hp _ _ _ _ Hl H) as [o [H1 Ho]].
      cbv beta in H1; apply ev_IfElse_fwd in H1.
      destruct H1 as [[Hc H1] | [Hc H1]].
      + rewrite evalExpr_And2_Not in Hc.
        change (andb (o @% "valid") (negb (o @% "data" @% "res" @% "writesF")) = true) in Hc.
        apply andb_true_iff in Hc; destruct Hc as [Hv Hw]; apply negb_true_iff in Hw.
        destruct (Ho Hv) as [x [xs [Hx [Hd Hready]]]].
        apply ev_LetAction in H1.
        rewrite (@evalActionPropGen_liftAction_child0Path "fus" _ [fusTree F xlen narrow (map fuL rest)] _ env) in H1.
        rewrite Hx in Hl.
        destruct (lo_deq _ _ _ _ _ _ Hp _ _ _ _ _ Hl Hready H1) as [sl' [H2 Hl']].
        cbn [evalActionPropGen] in H2.
        eexists _, _; split; [exact H2 | split; [cbn; discriminate |]]; intros _.
        exists 0%nat, x, xs; split; [exact Hx | split; [| split]].
        * rewrite <- Hd; reflexivity.
        * rewrite <- Hd; exact Hw.
        * cbn [FUsHold Fst Snd]; split; [exact Hl' |].
          apply (FUsHold_ext _ _ (fun i => f (S i))); [intros i; reflexivity | exact Hr].
      + rewrite (@evalActionPropGen_liftAction_child1Path "fus" _ _ [] _ env) in H1.
        destruct (IH _ _ (fun i => f (S i)) _ Hrest Hr H1) as [sr' [r [H2 [Hf Ht]]]].
        cbn [evalActionPropGen] in H2.
        eexists _, r; split; [exact H2 | split].
        * intros Hv; rewrite (Hf Hv); reflexivity.
        * intros Hv; destruct (Ht Hv) as [i [x [xs [Hx [Hd [Hw Hs]]]]]].
          exists (S i), x, xs; split; [exact Hx | split; [exact Hd | split; [exact Hw |]]].
          cbn [FUsHold Fst Snd]; split; [exact Hl |].
          apply (FUsHold_ext _ _ _ _ (fun j => eq_refl) Hs).
  Qed.

  (* ---------------------------------------------------------------------------
   * FU rules, through lenses
   * --------------------------------------------------------------------------- *)

  Variable lpsAll : list FUP.
  Local Abbreviation lsAll := (map fuL lpsAll).
  Local Abbreviation IT := (implTree F xlen narrow lsAll).
  Local Abbreviation St := (TreeState ElemState IT).

  (* The effect of a write-back of the fu output `o` (an `Option`) on the arch and control state. *)
  Definition wbUpdO (S : St) (o : type (Option OutK)) : St :=
    let A := S.(Fst) in
    let C := S.(Snd).(Fst) in
    let A1 := archSetFpr flen A (evalExpr ((#o)`"data"`"rd")) (evalExpr ((#o)`"data"`"res"`"res")) in
    let A2 := archSetFflags flen A1 (evalExpr (Or [ Var type (Bit 5) (archFflags flen A1) ; (#o)`"data"`"res"`"flags" ])) in
    let C1 := mkCtl (evalExpr (bitClrE type (Var type (Bit RegVecSz) C.(Fst)) ((#o)`"data"`"rd"))) C.(Snd).(Fst) C.(Snd).(Snd).(Fst) in
    (A2 ,, (C1 ,, S.(Snd).(Snd))).

  Record LensFwd {T : Tree Elem} (lf : forall k, Action type T k -> Action type IT k)
    (get : St -> TreeState ElemState T) (set : St -> TreeState ElemState T -> St) : Prop := {
    lens_ev : forall env k (a : Action type T k) S Q,
      evalActionPropGen env (lf k a) S Q ->
      exists env', evalActionPropGen env' a (get S) (fun t r => Q (set S t) r) ;
    lens_get_set : forall S t, get (set S t) = t ;
    lens_set_get : forall S, set S (get S) = S ;
    lens_get_wb : forall S o, get (wbUpdO S o) = get S
  }.

  Lemma lens_child0 : forall (L : FU F xlen narrow) (ls : list (FU F xlen narrow)) lf get set,
    @LensFwd (fusTree F xlen narrow (L :: ls)) lf get set ->
    @LensFwd (fuTree F xlen narrow L) (fun k a => lf k (liftAction child0Path a))
      (fun S => (get S).(Fst)) (fun S t => set S (t ,, (get S).(Snd))).
  Proof.
    intros L ls lf get set [Hev Hgs Hsg Hgw]; constructor.
    - intros env k a S Q H; destruct (Hev _ _ _ _ _ H) as [env' H1].
      cbn [fusTree] in *; destruct (get S) as [tl tr] eqn:Hg.
      rewrite evalActionPropGen_liftAction_child0Path in H1; eexists; exact H1.
    - intros S t; rewrite Hgs; reflexivity.
    - intros S; cbn [fusTree] in *.
      cbv beta; transitivity (set S (get S)); [| apply Hsg].
      f_equal; destruct (get S); reflexivity.
    - intros S o; rewrite Hgw; reflexivity.
  Qed.

  Lemma lens_child1 : forall (L : FU F xlen narrow) (ls : list (FU F xlen narrow)) lf get set,
    @LensFwd (fusTree F xlen narrow (L :: ls)) lf get set ->
    @LensFwd (fusTree F xlen narrow ls) (fun k a => lf k (liftAction child1Path a))
      (fun S => (get S).(Snd).(Fst)) (fun S t => set S ((get S).(Fst) ,, (t ,, tt))).
  Proof.
    intros L ls lf get set [Hev Hgs Hsg Hgw]; constructor.
    - intros env k a S Q H; destruct (Hev _ _ _ _ _ H) as [env' H1].
      cbn [fusTree] in *; destruct (get S) as [tl [tr []]] eqn:Hg.
      rewrite evalActionPropGen_liftAction_child1Path in H1; eexists; exact H1.
    - intros S t; rewrite Hgs; reflexivity.
    - intros S; cbn [fusTree] in *.
      cbv beta; transitivity (set S (get S)); [| apply Hsg].
      f_equal; destruct (get S) as [a [b []]]; reflexivity.
    - intros S o; rewrite Hgw; reflexivity.
  Qed.

  Lemma lens_fus :
    @LensFwd (fusTree F xlen narrow lsAll) (fun k a => liftFUs F xlen narrow lsAll type a)
      (fun S => S.(Snd).(Snd).(Fst)) (fun S t => (S.(Fst) ,, (S.(Snd).(Fst) ,, (t ,, tt)))).
  Proof.
    constructor.
    - intros env k a [A [C [Ls []]]] Q H; exact (ev_liftFUs _ _ _ _ a env A C Ls Q H).
    - reflexivity.
    - intros [A [C [Ls []]]]; reflexivity.
    - reflexivity.
  Qed.

  Lemma Retv_zero : forall (Q : St -> type (Bit 0) -> Prop) S (z : type (Bit 0)), Q S z -> Q S Zmod.zero.
  Proof. intros Q S z H; rewrite (bits0_eq Zmod.zero z); exact H. Qed.

  Lemma wbRule_fwd : forall L V (Hok : FUOk F xlen wlen narrow L V) lf get set (Hl : LensFwd lf get set)
    env S xs Q,
    lvHolds F xlen narrow L V (get S) xs ->
    evalActionPropGen env (wbRule F xlen narrow lsAll type L lf) S Q ->
    exists S', Q S' Zmod.zero /\
      (S' = S \/
       exists (o : type (Option OutK)) x rest t', xs = x :: rest /\ o @% "data" = fuSpec F xlen wlen narrow x /\
         (fuSpec F xlen wlen narrow x) @% "res" @% "writesF" = true /\
         lvHolds F xlen narrow L V t' rest /\ S' = set (wbUpdO S o) t').
  Proof.
    intros L V Hok lf get set Hl env S xs Q Hh H.
    unfold wbRule in H; apply ev_LetAction in H.
    destruct (lens_ev _ _ _ Hl _ _ _ _ _ H) as [env1 H0].
    destruct (lo_first _ _ _ _ _ _ Hok _ _ _ _ Hh H0) as [o [H1 Ho]].
    rewrite (lens_set_get _ _ _ Hl) in H1; cbv beta in H1; apply ev_IfElse_fwd in H1.
    destruct H1 as [[Hc H1] | [Hc H1]].
    - rewrite evalExpr_And2 in Hc.
      change (andb (o @% "valid") (o @% "data" @% "res" @% "writesF") = true) in Hc.
      apply andb_true_iff in Hc; destruct Hc as [Hv Hw].
      destruct (Ho Hv) as [x [xs' [Hx [Hd Hready]]]].
      destruct S as [A [[p [lp [ib []]]] [Ls []]]].
      cbn [evalActionPropGen] in H1.
      change (A ,, ((p ,, (lp ,, (ib ,, tt))) ,, (Ls ,, tt))) with (mkIT F xlen narrow lsAll A (mkCtl p lp ib) Ls) in H1.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFpr flen s _ _) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_archWriteFpr flen _ _ s P)) in H1.
      cbn [evalActionPropGen] in H1.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFflags flen s : type (Bit 5)))
                (fun env' s P => evalActionPropGen_archReadFflags flen s P)) in H1.
      cbn [evalActionPropGen] in H1.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFflags flen s _) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_archWriteFflags flen _ s P)) in H1.
      cbn [evalActionPropGen] in H1.
      rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (p : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadPend p lp ib P)) in H1.
      cbn [evalActionPropGen] in H1.
      rewrite (ev_liftCtl _ _ _ _ _ (fun _ => mkCtl _ lp ib) (fun _ => (Zmod.zero : type (Bit 0))) _ (fun env' P => ev_ctlWritePend p lp ib _ P)) in H1.
      cbn [evalActionPropGen] in H1.
      destruct (lens_ev _ _ _ Hl _ _ _ _ _ H1) as [env2 H2].
      set (S0 := mkIT F xlen narrow lsAll A (mkCtl p lp ib) Ls) in *.
      match type of H2 with evalActionPropGen _ _ (get ?S1) _ =>
        assert (Hg : get S1 = get S0) by (rewrite <- (lens_get_wb _ _ _ Hl S0 o); reflexivity);
        rewrite Hg in H2 end.
      unfold S0 in H2 |- *; rewrite Hx in Hh.
      destruct (lo_deq _ _ _ _ _ _ Hok _ _ _ _ _ Hh Hready H2) as [t' [H3 Ht']].
      cbn [evalActionPropGen] in H3.
      eexists; split; [eapply Retv_zero; exact H3 |].
      right; exists o, x, xs', t'; split; [exact Hx | split; [exact Hd | split; [rewrite <- Hd; exact Hw | split; [exact Ht' |]]]].
      reflexivity.
    - cbn [evalActionPropGen] in H1.
      eexists; split; [eapply Retv_zero; exact H1 | left; reflexivity].
  Qed.

  (* Every rule of the fus is a fu-internal step or a write-back of the head of one fu. *)
  Lemma fusRules_fwd : forall lps lf get set,
    @LensFwd (fusTree F xlen narrow (map fuL lps)) lf get set -> Forall FUOkP lps ->
    forall env r X g Q,
      FUsHold lps (get X) g ->
      In r (fusRules F xlen narrow type IT (wbRule F xlen narrow lsAll type) (map fuL lps) lf) ->
      evalActionPropGen env r X Q ->
      exists S', Q S' Zmod.zero /\
        ((exists t', S' = set X t' /\ FUsHold lps t' g) \/
         (exists (o : type (Option OutK)) i x rest t', g i = x :: rest /\
            o @% "data" = fuSpec F xlen wlen narrow x /\
            (fuSpec F xlen wlen narrow x) @% "res" @% "writesF" = true /\
            S' = set (wbUpdO X o) t' /\ FUsHold lps t' (setAt g i rest))).
  Proof.
    induction lps as [| p rest IH]; intros lf get set Hl Hok env r X g Q Hh Hin H; [destruct Hin |].
    apply Forall_cons_iff in Hok; destruct Hok as [Hp Hrest].
    pose proof (lens_child0 _ _ _ _ _ Hl) as Hl0.
    pose proof (lens_child1 _ _ _ _ _ Hl) as Hl1.
    cbn [FUsHold] in Hh; destruct Hh as [H0 H1].
    cbn [map fusRules] in Hin; destruct Hin as [<- | Hin].
    - (* write-back of fu 0 *)
      destruct (wbRule_fwd _ _ Hp _ _ _ Hl0 env X (g 0%nat) Q H0 H) as [S' [HQ [-> | [o [x [xs [t' [Hx [Hd [Hw [Ht ->]]]]]]]]]]].
      + exists X; split; [exact HQ |]; left; exists (get X); split; [symmetry; apply (lens_set_get _ _ _ Hl) |].
        split; [exact H0 | exact H1].
      + eexists; split; [exact HQ |]; right.
        exists o, 0%nat, x, xs, (t' ,, (get X).(Snd)); split; [exact Hx | split; [exact Hd | split; [exact Hw | split]]].
        * cbv beta; rewrite (lens_get_wb _ _ _ Hl); reflexivity.
        * cbn [FUsHold Fst Snd]; split; [exact Ht |].
          apply (FUsHold_ext _ _ (fun i => g (S i))); [intros i; reflexivity | exact H1].
    - apply in_app_or in Hin; destruct Hin as [Hin | Hin].
      + (* fu-internal rule of fu 0 *)
        apply in_map_iff in Hin; destruct Hin as [r' [<- Hin]].
        destruct (lens_ev _ _ _ Hl0 _ _ _ _ _ H) as [env' H'].
        destruct (lo_rules _ _ _ _ _ _ Hp _ _ _ _ _ Hin H0 H') as [t' [HQ Ht]].
        eexists; split; [exact HQ |]; left.
        exists (t' ,, (get X).(Snd)); split; [reflexivity |].
        cbn [FUsHold Fst Snd]; split; [exact Ht | exact H1].
      + (* a rule of the other fus *)
        destruct (IH _ _ _ Hl1 Hrest env r X (fun i => g (S i)) Q H1 Hin H)
          as [S' [HQ [[t' [-> Ht]] | [o [i [x [xs [t' [Hx [Hd [Hw [-> Ht]]]]]]]]]]]].
        * eexists; split; [exact HQ |]; left.
          exists ((get X).(Fst) ,, (t' ,, tt)); split; [reflexivity |].
          cbn [FUsHold Fst Snd]; split; [exact H0 | exact Ht].
        * eexists; split; [exact HQ |]; right.
          exists o, (S i), x, xs, ((get X).(Fst) ,, (t' ,, tt)); split; [exact Hx | split; [exact Hd | split; [exact Hw | split]]].
          -- cbv beta; rewrite (lens_get_wb _ _ _ Hl); reflexivity.
          -- cbn [FUsHold Fst Snd]; split; [exact H0 |].
             apply (FUsHold_ext _ _ _ _ (fun j => eq_refl) Ht).
  Qed.

  Lemma implRules_fwd : Forall FUOkP lpsAll ->
    forall env r (X : St) g Q,
      FUsHold lpsAll X.(Snd).(Snd).(Fst) g ->
      In r (fpuImplRules F xlen narrow lsAll type) ->
      evalActionPropGen env r X Q ->
      exists S', Q S' Zmod.zero /\
        ((exists t', S' = (X.(Fst) ,, (X.(Snd).(Fst) ,, (t' ,, tt))) /\ FUsHold lpsAll t' g) \/
         (exists (o : type (Option OutK)) i x rest t', g i = x :: rest /\
            o @% "data" = fuSpec F xlen wlen narrow x /\
            (fuSpec F xlen wlen narrow x) @% "res" @% "writesF" = true /\
            S' = ((wbUpdO X o).(Fst) ,, ((wbUpdO X o).(Snd).(Fst) ,, (t' ,, tt))) /\
            FUsHold lpsAll t' (setAt g i rest))).
  Proof.
    intros Hok env r X g Q Hh Hin H.
    exact (fusRules_fwd lpsAll _ _ _ lens_fus Hok env r X g Q Hh Hin H).
  Qed.
End FUs.

(* ===========================================================================
 * 4. INTERFACE ACTIONS
 * =========================================================================== *)

Lemma if_fwd : forall (b : bool) (P Q : Prop), (if b then P else Q) -> (b = true /\ P) \/ (b = false /\ Q).
Proof. intros [|] P Q H; auto. Qed.

Definition busyF (p lp : bits RegVecSz) (r : bits FprIdxSz) : bool := orb (bitOf p r) (bitOf lp r).

Lemma evalExpr_bitTestE' : forall (w : bits RegVecSz) (e : Expr type (Bit FprIdxSz)),
  evalExpr (bitTestE type (Var type (Bit RegVecSz) w) e) = bitOf w (evalExpr e).
Proof. intros w e; exact (evalExpr_bitTestE w (evalExpr e)). Qed.

Lemma evalExpr_busyE : forall (p lp : bits RegVecSz) (e : Expr type (Bit FprIdxSz)),
  evalExpr (busyE type p lp e) = busyF p lp (evalExpr e).
Proof.
  intros p lp e; unfold busyE, busyF; cbn [evalExpr fold_left map evalOrBinary evalBinary KindCustomInd getDefault].
  rewrite !evalExpr_bitTestE'; reflexivity.
Qed.

Definition sbOkF {narrow : list FpFmt} (p lp : bits RegVecSz) (ib : bool) (pkt : type (FpuPktK narrow)) (wf : bool) : bool :=
  negb (busyF p lp (pktRs1 pkt)) && negb (busyF p lp (pktRs2 pkt)) && negb (busyF p lp (pktRs3 pkt)) &&
  (if wf then negb (busyF p lp (pktRd pkt)) else negb ib).

Lemma evalExpr_sbOkE : forall narrow p lp ib pkt wf, evalExpr (sbOkE narrow type p lp ib pkt wf) = sbOkF p lp ib pkt wf.
Proof.
  intros narrow p lp ib pkt wf; unfold sbOkE, sbOkF; cbn [evalExpr fold_left map evalNot KindCustomInd].
  rewrite !evalExpr_busyE; destruct wf; reflexivity.
Qed.

Lemma bitOf_set' : forall (w : bits RegVecSz) (e : Expr type (Bit FprIdxSz)) j,
  bitOf (evalExpr (bitSetE type (Var type (Bit RegVecSz) w) e)) j = if Zmod.eqb j (evalExpr e) then true else bitOf w j.
Proof. intros w e j; exact (bitOf_set w (evalExpr e) j). Qed.

Lemma bitOf_clr' : forall (w : bits RegVecSz) (e : Expr type (Bit FprIdxSz)) j,
  bitOf (evalExpr (bitClrE type (Var type (Bit RegVecSz) w) e)) j = if Zmod.eqb j (evalExpr e) then false else bitOf w j.
Proof. intros w e j; exact (bitOf_clr w (evalExpr e) j). Qed.

Section Interface.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.
  Variable lps : list (FUP F xlen narrow).

  Local Abbreviation InK := (FUInK F xlen narrow).
  Local Abbreviation ls := (map (fuL F xlen narrow) lps).
  Local Abbreviation IT := (implTree F xlen narrow ls).
  Local Abbreviation mkS := (mkIT F xlen narrow ls).

  Definition wfOf (pkt : type (FpuPktK narrow)) : bool := negb (opWritesXV narrow (pkt @% "op")).

  (* The fu input built at issue. *)
  Definition inpOf (A : ArchSt flen) (pkt : type (FpuPktK narrow)) (x : bits xlen) : type InK :=
    (pkt ,, (rmOf pkt (archFrm flen A) ,, (archFpr flen A (pktRs1 pkt) ,, (archFpr flen A (pktRs2 pkt) ,,
     (archFpr flen A (pktRs3 pkt) ,, (x ,, tt)))))).

  Definition bitSetV (w : bits RegVecSz) (r : bits FprIdxSz) : bits RegVecSz :=
    evalExpr (bitSetE type (Var type (Bit RegVecSz) w) (Var type (Bit FprIdxSz) r)).
  Definition bitClrV (w : bits RegVecSz) (r : bits FprIdxSz) : bits RegVecSz :=
    evalExpr (bitClrE type (Var type (Bit RegVecSz) w) (Var type (Bit FprIdxSz) r)).

  Lemma fpuIssue_fwd : forall (env : Env IT) A p lp ib Ls pkt x Q f,
    Forall (FUOkP F xlen wlen narrow) lps -> FUsHold F xlen narrow lps Ls f ->
    evalActionPropGen env (fpuIssue F xlen narrow ls type pkt x) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (ok : bool), Q S' ok /\
      (ok = false -> S' = mkS A (mkCtl p lp ib) Ls) /\
      (ok = true -> sbOkF p lp ib pkt (wfOf pkt) = true /\
         exists i Ls', route F xlen narrow lps pkt = Some i /\
           FUsHold F xlen narrow lps Ls' (setAt F xlen narrow f i (f i ++ [inpOf A pkt x])) /\
           S' = mkS (archSetFs flen A dirtyZ) (if wfOf pkt then mkCtl (bitSetV p (pktRd pkt)) lp ib else mkCtl p lp true) Ls').
  Proof.
    intros env A p lp ib Ls pkt x Q f Hok Hh H.
    unfold fpuIssue in H; cbn [evalActionPropGen] in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (p : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadPend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (lp : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadLpend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (ib : type Bool)) _ (fun env' P => ev_ctlReadIntBusy p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFrm flen s : type (Bit 3)))
              (fun env' s P => evalActionPropGen_archReadFrm flen s P)) in H.
    cbn beta in H.
    do 3 (rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFpr flen s (evalExpr (_ : Expr type (Bit FprIdxSz))) : type (Bit flen)))
              (fun env' s P => evalActionPropGen_archReadFpr flen _ s P)) in H; cbn beta in H).
    apply ev_liftFUs in H; destruct H as [env1 H].
    destruct (tryEnqFUs_fwd F xlen wlen narrow lps env1 Ls f _ pkt (inpOf A pkt x) _ Hok Hh eq_refl H)
      as [Ls' [b [H1 [Hf Ht]]]].
    cbv beta in H1.
    destruct b.
    - destruct (Ht eq_refl) as [Hgo [i [Hi Hl']]].
      cbn [evalExpr] in H1; apply if_fwd in H1.
      destruct H1 as [[Hw H1] | [Hw H1]].
      + change (wfOf pkt = true) in Hw.
        cbn [evalActionPropGen] in H1.
        rewrite (ev_liftCtl _ _ _ _ _ (fun _ => mkCtl _ lp ib) (fun _ => (Zmod.zero : type (Bit 0))) _ (fun env' P => ev_ctlWritePend p lp ib _ P)) in H1.
        cbn beta in H1.
        rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFs flen s _) (fun _ => (Zmod.zero : type (Bit 0)))
                  (fun env' s P => evalActionPropGen_archWriteFs flen _ s P)) in H1.
        cbn [evalActionPropGen] in H1.
        eexists _, true; split; [exact H1 | split; [discriminate |]]; intros _.
        split; [rewrite <- evalExpr_sbOkE; exact Hgo |].
        exists i, Ls'; split; [exact Hi | split; [exact Hl' |]].
        rewrite Hw; reflexivity.
      + change (wfOf pkt = false) in Hw.
        cbn [evalActionPropGen] in H1.
        rewrite (ev_liftCtl _ _ _ _ _ (fun _ => mkCtl p lp _) (fun _ => (Zmod.zero : type (Bit 0))) _ (fun env' P => ev_ctlWriteIntBusy p lp ib _ P)) in H1.
        cbn beta in H1.
        rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFs flen s _) (fun _ => (Zmod.zero : type (Bit 0)))
                  (fun env' s P => evalActionPropGen_archWriteFs flen _ s P)) in H1.
        cbn [evalActionPropGen] in H1.
        eexists _, true; split; [exact H1 | split; [discriminate |]]; intros _.
        split; [rewrite <- evalExpr_sbOkE; exact Hgo |].
        exists i, Ls'; split; [exact Hi | split; [exact Hl' |]].
        rewrite Hw; reflexivity.
    - rewrite (Hf eq_refl) in H1; cbn [evalExpr evalActionPropGen] in H1.
      eexists _, false; split; [exact H1 | split; [reflexivity | discriminate]].
  Qed.

  Lemma fpuIntResp_fwd : forall (env : Env IT) A p lp ib Ls Q f,
    Forall (FUOkP F xlen wlen narrow) lps -> FUsHold F xlen narrow lps Ls f ->
    evalActionPropGen env (fpuIntResp F xlen narrow ls type) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (r : type (Option (Bit xlen))), Q S' r /\
      (r @% "valid" = false -> S' = mkS A (mkCtl p lp ib) Ls) /\
      (r @% "valid" = true -> exists i x rest Ls', f i = x :: rest /\
         (fuSpec F xlen wlen narrow x) @% "res" @% "writesF" = false /\
         r @% "data" = (fuSpec F xlen wlen narrow x) @% "res" @% "xres" /\
         FUsHold F xlen narrow lps Ls' (setAt F xlen narrow f i rest) /\
         S' = mkS (archSetFflags flen A (Zmod.or (archFflags flen A) ((fuSpec F xlen wlen narrow x) @% "res" @% "flags")))
                  (mkCtl p lp false) Ls').
  Proof.
    intros env A p lp ib Ls Q f Hok Hh H.
    unfold fpuIntResp in H; cbn [evalActionPropGen] in H.
    apply ev_liftFUs in H; destruct H as [env1 H].
    destruct (intRespFUs_fwd F xlen wlen narrow lps env1 Ls f _ Hok Hh H) as [Ls' [r [H1 [Hf Ht]]]].
    cbv beta in H1; apply if_fwd in H1; destruct H1 as [[Hv H1] | [Hv H1]].
    - change (r @% "valid" = true) in Hv.
      destruct (Ht Hv) as [i [x [xs [Hx [Hd [Hw Hl']]]]]].
      cbn [evalActionPropGen] in H1.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFflags flen s : type (Bit 5)))
                (fun env' s P => evalActionPropGen_archReadFflags flen s P)) in H1.
      cbn beta in H1.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFflags flen s _) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_archWriteFflags flen _ s P)) in H1.
      cbn beta in H1.
      rewrite (ev_liftCtl _ _ _ _ _ (fun _ => mkCtl p lp _) (fun _ => (Zmod.zero : type (Bit 0))) _ (fun env' P => ev_ctlWriteIntBusy p lp ib _ P)) in H1.
      cbn [evalActionPropGen] in H1.
      eexists _, _; split; [exact H1 |]; split; [intros Hc; change (r @% "valid" = false) in Hc; rewrite Hv in Hc; discriminate |]; intros _.
      exists i, x, xs, Ls'; split; [exact Hx | split; [exact Hw | split; [| split; [exact Hl' |]]]].
      + rewrite <- Hd; reflexivity.
      + rewrite evalExpr_Or2, <- Hd; reflexivity.
    - change (r @% "valid" = false) in Hv.
      rewrite (Hf Hv) in H1; cbn [evalActionPropGen] in H1.
      eexists _, _; split; [exact H1 | split; [reflexivity | intros Hc; change (r @% "valid" = true) in Hc; rewrite Hv in Hc; discriminate]].
  Qed.

  Lemma fpuReserve_fwd : forall (env : Env IT) A p lp ib Ls rd Q,
    evalActionPropGen env (fpuReserve F xlen narrow ls type rd) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (ok : bool), Q S' ok /\ ok = negb (busyF p lp rd) /\
      S' = (if ok then mkS (archSetFs flen A dirtyZ) (mkCtl p (bitSetV lp rd) ib) Ls else mkS A (mkCtl p lp ib) Ls).
  Proof.
    intros env A p lp ib Ls rd Q H.
    unfold fpuReserve in H; cbn [evalActionPropGen] in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (p : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadPend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (lp : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadLpend p lp ib P)) in H.
    cbn beta in H.
    apply if_fwd in H; destruct H as [[Hc H] | [Hc H]].
    - cbn [evalActionPropGen] in H.
      rewrite (ev_liftCtl _ _ _ _ _ (fun _ => mkCtl p _ ib) (fun _ => (Zmod.zero : type (Bit 0))) _ (fun env' P => ev_ctlWriteLpend p lp ib _ P)) in H.
      cbn beta in H.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFs flen s _) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_archWriteFs flen _ s P)) in H.
      cbn [evalActionPropGen] in H.
      cbn [evalExpr evalNot KindCustomInd] in Hc; rewrite evalExpr_busyE in Hc.
      eexists _, _; split; [exact H |].
      split; cbn [evalExpr evalNot KindCustomInd]; rewrite evalExpr_busyE; [reflexivity | rewrite Hc; reflexivity].
    - cbn [evalActionPropGen] in H.
      cbn [evalExpr evalNot KindCustomInd] in Hc; rewrite evalExpr_busyE in Hc.
      eexists _, _; split; [exact H |].
      split; cbn [evalExpr evalNot KindCustomInd]; rewrite evalExpr_busyE; [reflexivity | rewrite Hc; reflexivity].
  Qed.

  Lemma fpuFill_fwd : forall (env : Env IT) A p lp ib Ls rd v Q,
    evalActionPropGen env (fpuFill F xlen narrow ls type rd v) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (ok : bool), Q S' ok /\ ok = bitOf lp rd /\
      S' = (if ok then mkS (archSetFpr flen A rd v) (mkCtl p (bitClrV lp rd) ib) Ls else mkS A (mkCtl p lp ib) Ls).
  Proof.
    intros env A p lp ib Ls rd v Q H.
    unfold fpuFill in H; cbn [evalActionPropGen] in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (lp : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadLpend p lp ib P)) in H.
    cbn beta in H.
    apply if_fwd in H; destruct H as [[Hc H] | [Hc H]].
    - cbn [evalActionPropGen] in H.
      rewrite (ev_liftArch _ _ _ _ _ (fun s => archSetFpr flen s _ _) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_archWriteFpr flen _ _ s P)) in H.
      cbn beta in H.
      rewrite (ev_liftCtl _ _ _ _ _ (fun _ => mkCtl p _ ib) (fun _ => (Zmod.zero : type (Bit 0))) _ (fun env' P => ev_ctlWriteLpend p lp ib _ P)) in H.
      cbn [evalActionPropGen] in H.
      cbn [evalExpr] in Hc; rewrite evalExpr_bitTestE' in Hc.
      eexists _, _; split; [exact H |].
      split; cbn [evalExpr]; rewrite evalExpr_bitTestE'; [reflexivity | rewrite Hc; reflexivity].
    - cbn [evalActionPropGen] in H.
      cbn [evalExpr] in Hc; rewrite evalExpr_bitTestE' in Hc.
      eexists _, _; split; [exact H |].
      split; cbn [evalExpr]; rewrite evalExpr_bitTestE'; [reflexivity | rewrite Hc; reflexivity].
  Qed.

  Lemma fpuReadT_fwd : forall (env : Env IT) A p lp ib Ls idx Q,
    evalActionPropGen env (fpuReadT F xlen narrow ls type idx) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists r : type (Option (Bit flen)), Q (mkS A (mkCtl p lp ib) Ls) r /\
      r @% "data" = archFpr flen A idx /\ r @% "valid" = negb (busyF p lp idx).
  Proof.
    intros env A p lp ib Ls idx Q H.
    unfold fpuReadT in H; cbn [evalActionPropGen] in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (p : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadPend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (lp : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadLpend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFpr flen s idx : type (Bit flen)))
              (fun env' s P => evalActionPropGen_fpuRead F (Var type (Bit FprIdxSz) idx) s P)) in H.
    cbn [evalActionPropGen] in H.
    eexists; split; [exact H | split; [reflexivity |]].
    change (negb (evalExpr (busyE type p lp (Var type (Bit FprIdxSz) idx))) = negb (busyF p lp idx)).
    rewrite evalExpr_busyE; reflexivity.
  Qed.

  Lemma fpuWriteT_fwd : forall (env : Env IT) A p lp ib Ls idx v Q,
    evalActionPropGen env (fpuWriteT F xlen narrow ls type idx v) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (ok : bool), Q S' ok /\ ok = negb (busyF p lp idx) /\
      S' = (if ok then mkS (writeSem F A idx v) (mkCtl p lp ib) Ls else mkS A (mkCtl p lp ib) Ls).
  Proof.
    intros env A p lp ib Ls idx v Q H.
    unfold fpuWriteT in H; cbn [evalActionPropGen] in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (p : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadPend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (lp : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadLpend p lp ib P)) in H.
    cbn beta in H.
    apply if_fwd in H; destruct H as [[Hc H] | [Hc H]].
    - rewrite (ev_liftArch _ _ _ _ _ (fun s => writeSem F s idx v) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_fpuWrite F (Var type _ idx) (Var type _ v) s P)) in H.
      cbn [evalActionPropGen] in H.
      cbn [evalExpr evalNot KindCustomInd] in Hc; rewrite evalExpr_busyE in Hc.
      eexists _, _; split; [exact H |].
      split; cbn [evalExpr evalNot KindCustomInd]; rewrite evalExpr_busyE; [reflexivity | rewrite Hc; reflexivity].
    - cbn [evalActionPropGen] in H.
      cbn [evalExpr evalNot KindCustomInd] in Hc; rewrite evalExpr_busyE in Hc.
      eexists _, _; split; [exact H |].
      split; cbn [evalExpr evalNot KindCustomInd]; rewrite evalExpr_busyE; [reflexivity | rewrite Hc; reflexivity].
  Qed.

  Definition drainedF (p : bits RegVecSz) (ib : bool) : bool := Zmod.eqb p (Zmod.of_Z (2 ^ RegVecSz) 0) && negb ib.

  Lemma fpuDrained_fwd : forall (env : Env IT) A p lp ib Ls Q,
    evalActionPropGen env (fpuDrained F xlen narrow ls type) (mkS A (mkCtl p lp ib) Ls) Q ->
    Q (mkS A (mkCtl p lp ib) Ls) (drainedF p ib).
  Proof.
    intros env A p lp ib Ls Q H.
    unfold fpuDrained in H; cbn [evalActionPropGen] in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (p : type (Bit RegVecSz))) _ (fun env' P => ev_ctlReadPend p lp ib P)) in H.
    cbn beta in H.
    rewrite (ev_liftCtl _ _ _ _ _ (fun c => c) (fun _ => (ib : type Bool)) _ (fun env' P => ev_ctlReadIntBusy p lp ib P)) in H.
    cbn [evalActionPropGen] in H.
    exact H.
  Qed.

  Lemma fpuFflagsWriteT_fwd : forall (env : Env IT) A p lp ib Ls v Q,
    evalActionPropGen env (fpuFflagsWriteT F xlen narrow ls type v) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (ok : bool), Q S' ok /\ ok = drainedF p ib /\
      S' = (if ok then mkS (fflagsWriteSem F A v) (mkCtl p lp ib) Ls else mkS A (mkCtl p lp ib) Ls).
  Proof.
    intros env A p lp ib Ls v Q H.
    unfold fpuFflagsWriteT in H; cbn [evalActionPropGen] in H.
    apply fpuDrained_fwd in H; cbv beta in H.
    destruct (drainedF p ib) eqn:Hd; cbn [evalExpr evalActionPropGen] in H.
    - rewrite (ev_liftArch _ _ _ _ _ (fun s => fflagsWriteSem F s v) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_fflagsWrite F (Var type _ v) s P)) in H.
      cbn [evalActionPropGen] in H.
      eexists _, true; split; [exact H | split; reflexivity].
    - eexists _, false; split; [exact H | split; reflexivity].
  Qed.

  Lemma fpuFcsrWriteT_fwd : forall (env : Env IT) A p lp ib Ls v Q,
    evalActionPropGen env (fpuFcsrWriteT F xlen narrow ls type v) (mkS A (mkCtl p lp ib) Ls) Q ->
    exists S' (ok : bool), Q S' ok /\ ok = drainedF p ib /\
      S' = (if ok then mkS (fcsrWriteSem F A v) (mkCtl p lp ib) Ls else mkS A (mkCtl p lp ib) Ls).
  Proof.
    intros env A p lp ib Ls v Q H.
    unfold fpuFcsrWriteT in H; cbn [evalActionPropGen] in H.
    apply fpuDrained_fwd in H; cbv beta in H.
    destruct (drainedF p ib) eqn:Hd; cbn [evalExpr evalActionPropGen] in H.
    - rewrite (ev_liftArch _ _ _ _ _ (fun s => fcsrWriteSem F s v) (fun _ => (Zmod.zero : type (Bit 0)))
                (fun env' s P => evalActionPropGen_fcsrWrite F (Var type _ v) s P)) in H.
      cbn [evalActionPropGen] in H.
      eexists _, true; split; [exact H | split; reflexivity].
    - eexists _, false; split; [exact H | split; reflexivity].
  Qed.

  Lemma fpuFflagsReadT_fwd : forall (env : Env IT) A p lp ib Ls Q,
    evalActionPropGen env (fpuFflagsReadT F xlen narrow ls type) (mkS A (mkCtl p lp ib) Ls) Q ->
    Q (mkS A (mkCtl p lp ib) Ls) (archFflags flen A ,, (drainedF p ib ,, tt)).
  Proof.
    intros env A p lp ib Ls Q H.
    unfold fpuFflagsReadT in H; cbn [evalActionPropGen] in H.
    apply fpuDrained_fwd in H; cbv beta in H.
    rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFflags flen s : type (Bit 5)))
              (fun env' s P => evalActionPropGen_fflagsRead F s P)) in H.
    cbn [evalActionPropGen] in H; exact H.
  Qed.

  Lemma fpuFcsrReadT_fwd : forall (env : Env IT) A p lp ib Ls Q,
    evalActionPropGen env (fpuFcsrReadT F xlen narrow ls type) (mkS A (mkCtl p lp ib) Ls) Q ->
    Q (mkS A (mkCtl p lp ib) Ls) (fcsrOf F A ,, (drainedF p ib ,, tt)).
  Proof.
    intros env A p lp ib Ls Q H.
    unfold fpuFcsrReadT in H; cbn [evalActionPropGen] in H.
    apply fpuDrained_fwd in H; cbv beta in H.
    rewrite (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (fcsrOf F s : type (Bit 8)))
              (fun env' s P => evalActionPropGen_fcsrRead F s P)) in H.
    cbn [evalActionPropGen] in H; exact H.
  Qed.

  Lemma ev_fpuFrmRead : forall (env : Env IT) A C Ls Q,
    evalActionPropGen env (fpuFrmRead F xlen narrow ls type) (mkS A C Ls) Q <-> Q (mkS A C Ls) (archFrm flen A).
  Proof. intros; apply (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFrm flen s : type (Bit 3))) (fun env' s P => evalActionPropGen_frmRead F s P)). Qed.

  Lemma ev_fpuFrmWrite : forall (env : Env IT) A C Ls v Q,
    evalActionPropGen env (fpuFrmWrite F xlen narrow ls type v) (mkS A C Ls) Q <-> Q (mkS (frmWriteSem F A v) C Ls) Zmod.zero.
  Proof. intros; apply (ev_liftArch _ _ _ _ _ (fun s => frmWriteSem F s v) (fun _ => (Zmod.zero : type (Bit 0))) (fun env' s P => evalActionPropGen_frmWrite F (Var type _ v) s P)). Qed.

  Lemma ev_fpuFsRead : forall (env : Env IT) A C Ls Q,
    evalActionPropGen env (fpuFsRead F xlen narrow ls type) (mkS A C Ls) Q <-> Q (mkS A C Ls) (archFs flen A).
  Proof. intros; apply (ev_liftArch _ _ _ _ _ (fun s => s) (fun s => (archFs flen s : type (Bit 2))) (fun env' s P => evalActionPropGen_fsRead F s P)). Qed.

  Lemma ev_fpuFsWrite : forall (env : Env IT) A C Ls v Q,
    evalActionPropGen env (fpuFsWrite F xlen narrow ls type v) (mkS A C Ls) Q <-> Q (mkS (fsWriteSem F A v) C Ls) Zmod.zero.
  Proof. intros; apply (ev_liftArch _ _ _ _ _ (fun s => fsWriteSem F s v) (fun _ => (Zmod.zero : type (Bit 0))) (fun env' s P => evalActionPropGen_fsWrite F (Var type _ v) s P)). Qed.
End Interface.

Arguments wfOf {narrow} pkt.
