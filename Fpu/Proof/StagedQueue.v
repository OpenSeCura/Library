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
 * Queue view of the staged controllers (`StagedQueue.v`).
 *
 * A staged controller of `ImplStaged.v` behaves as a FIFO of inputs whose head, when ready,
 * yields `finishFn (stepFn^n (initFn x))`.  This file gives, for both controllers, a relation
 * `Holds s xs` ("state `s` holds the inputs `xs`, oldest first") and forward lemmas for every
 * action and rule:
 * - `enq` appends (when `canEnq` said yes),
 * - every internal rule keeps `xs`,
 * - `first`, when valid, returns the spec value of the head of `xs` and makes `deq` legal,
 * - `deq` drops the head,
 * - the initial state holds `[]`.
 *
 * Pipelined (`stagedPipe*`): `PipeHolds k n s xs` -- the slot at depth `j` (with `k + j` steps
 * done) holds `StageValAt (k + j) x`.  Iterative (`stagedIter*`): `IterHolds s xs` -- idle with
 * `xs = []`, or busy on the single input `x` after `m` steps.
 *)

From Stdlib Require Import String List ZArith Znumtheory Zmod Zmod.Bits Lia Bool Eqdep_dec.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas ActionSim.
From Fpu Require Export ShiftFifoLemmas ImplStaged ImplStagedProof.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Open Scope list_scope.

(* ===========================================================================
 * 1. ONE-ELEMENT FIFO AS AN OPTION
 * =========================================================================== *)

Definition fifoVal {K : Kind} (f : TreeState ElemState (fifoTree 1 K)) : option (type K) :=
  if Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 0) then None else Some (fifo1_elem f).

Lemma bits1_cases : forall (sz : bits 1), sz = Zmod.of_Z 2 0 \/ sz = Zmod.of_Z 2 1.
Proof.
  intros sz.
  destruct (Zmod.eqb sz (Zmod.of_Z 2 1)) eqn:H1.
  - right; apply Zmod.eqb_eq in H1; exact H1.
  - left; apply bits1_not_one_is_zero; exact H1.
Qed.

Lemma fifoVal_None_size : forall {K} (f : TreeState ElemState (fifoTree 1 K)),
  fifoVal f = None -> fifo1_size f = Zmod.of_Z 2 0.
Proof.
  intros K f; unfold fifoVal.
  destruct (bits1_cases (fifo1_size f)) as [H | H]; rewrite H; [auto | discriminate].
Qed.

Lemma fifoVal_Some_size : forall {K} (f : TreeState ElemState (fifoTree 1 K)) v,
  fifoVal f = Some v -> fifo1_size f = Zmod.of_Z 2 1 /\ fifo1_elem f = v.
Proof.
  intros K f v; unfold fifoVal.
  destruct (bits1_cases (fifo1_size f)) as [H | H]; rewrite H; [discriminate |].
  intros Hv; injection Hv; auto.
Qed.

Lemma fifoVal_full : forall {K} (f : TreeState ElemState (fifoTree 1 K)),
  fifo1_size f = Zmod.of_Z 2 1 -> fifoVal f = Some (fifo1_elem f).
Proof. intros K f H; unfold fifoVal; rewrite H; reflexivity. Qed.

Lemma fifoVal_empty : forall {K} (f : TreeState ElemState (fifoTree 1 K)),
  fifo1_size f = Zmod.of_Z 2 0 -> fifoVal f = None.
Proof. intros K f H; unfold fifoVal; rewrite H; reflexivity. Qed.

(* The slot `f` on top of the older items `ys` represents `xs`. *)
Definition slotHolds {InpK K : Kind} (sv : type InpK -> type K)
  (f : TreeState ElemState (fifoTree 1 K)) (ys xs : list (type InpK)) : Prop :=
  match fifoVal f with
  | None => xs = ys
  | Some v => exists x, xs = ys ++ [x] /\ v = sv x
  end.

(* ===========================================================================
 * 2. PIPELINED CONTROLLER
 * =========================================================================== *)

Section PipeQueue.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Variable initFn   : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn   : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn : forall ty, ty StateK -> LetExpr ty OutK.

  Local Abbreviation stagesTree n := (stagedStagesTree StateK n).
  Local Abbreviation SV := (StageValAt initFn stepFn).

  Fixpoint PipeHolds (k n : nat) : TreeState ElemState (stagesTree n) -> list (type InpK) -> Prop :=
    match n return TreeState ElemState (stagesTree n) -> list (type InpK) -> Prop with
    | 0%nat => fun s xs => slotHolds (SV k) s.(Fst) [] xs
    | S m   => fun s xs => exists ys, PipeHolds (S k) m s.(Snd).(Fst) ys /\ slotHolds (SV k) s.(Fst) ys xs
    end.

  Definition pipeSetHead (n : nat) (s : TreeState ElemState (stagesTree n))
    (f : TreeState ElemState (fifoTree 1 StateK)) : TreeState ElemState (stagesTree n) :=
    (f ,, s.(Snd)).

  (* Filling the empty entry slot appends. *)
  Lemma PipeHolds_fill_head : forall k n (s : TreeState ElemState (stagesTree n)) xs x f',
    PipeHolds k n s xs -> fifoVal s.(Fst) = None -> fifoVal f' = Some (SV k x) ->
    PipeHolds k n (pipeSetHead n s f') (xs ++ [x]).
  Proof.
    intros k [| m] s xs x f' Hh Hn Hf; cbn [PipeHolds pipeSetHead Fst Snd] in *.
    - unfold slotHolds in *; rewrite Hn in Hh; rewrite Hf; subst xs; exists x; split; reflexivity.
    - destruct Hh as [ys [Hys Hsl]]; exists ys; split; [exact Hys |].
      unfold slotHolds in *; rewrite Hn in Hsl; rewrite Hf; subst xs; exists x; split; reflexivity.
  Qed.

  (* The deepest slot, when full, holds the oldest item. *)
  Lemma PipeHolds_last : forall n k (s : TreeState ElemState (stagesTree n)) xs v,
    PipeHolds k n s xs -> fifoVal (stagedLastFifo StateK n s) = Some v ->
    exists x rest, xs = x :: rest /\ v = SV (k + n) x.
  Proof.
    induction n as [| m IH]; intros k s xs v Hh Hv; cbn [PipeHolds stagedLastFifo] in *.
    - unfold slotHolds in Hh; rewrite Hv in Hh; destruct Hh as [x [-> ->]].
      exists x, []; rewrite Nat.add_0_r; split; reflexivity.
    - destruct Hh as [ys [Hys Hsl]].
      destruct (IH (S k) _ ys v Hys Hv) as [x [rest [-> Hx]]].
      unfold slotHolds in Hsl; destruct (fifoVal s.(Fst)) as [w |].
      + destruct Hsl as [z [-> _]]; exists x, (rest ++ [z]); split; [reflexivity |].
        rewrite Hx; f_equal; lia.
      + subst xs; exists x, rest; split; [reflexivity |]; rewrite Hx; f_equal; lia.
  Qed.

  Lemma stagedLast_update_same : forall n (s : TreeState ElemState (stagesTree n)) f',
    stagedLastFifo StateK n (stagedUpdateLastFifo StateK n s f') = f'.
  Proof.
    induction n as [| m IH]; intros s f';
      [destruct s as [f0 []]; reflexivity
      | destruct s as [f_head [st_tail []]]; cbn [stagedUpdateLastFifo stagedLastFifo Fst Snd]; apply IH].
  Qed.

  Lemma stagedUpdate_last_id : forall n (s : TreeState ElemState (stagesTree n)),
    stagedUpdateLastFifo StateK n s (stagedLastFifo StateK n s) = s.
  Proof.
    induction n as [| m IH]; intros s;
      [destruct s as [f0 []]; reflexivity
      | destruct s as [f_head [st_tail []]]; cbn [stagedUpdateLastFifo stagedLastFifo Fst Snd]; rewrite IH; reflexivity].
  Qed.

  (* Emptying the deepest slot drops the oldest item. *)
  Lemma PipeHolds_drop_last : forall n k (s : TreeState ElemState (stagesTree n)) x rest f',
    PipeHolds k n s (x :: rest) -> fifoVal (stagedLastFifo StateK n s) <> None -> fifoVal f' = None ->
    PipeHolds k n (stagedUpdateLastFifo StateK n s f') rest.
  Proof.
    induction n as [| m IH]; intros k s x rest f' Hh Hv Hf.
    - destruct s as [f0 []]; cbn [PipeHolds stagedLastFifo stagedUpdateLastFifo Fst Snd] in *.
      unfold slotHolds in *; rewrite Hf.
      destruct (fifoVal f0) as [w |]; [| discriminate].
      destruct Hh as [z [Hz _]]; cbn in Hz; injection Hz as _ ->; reflexivity.
    - destruct s as [f0 [sub []]]; cbn [PipeHolds stagedLastFifo stagedUpdateLastFifo Fst Snd] in *.
      destruct Hh as [ys [Hys Hsl]].
      destruct (fifoVal (stagedLastFifo StateK m sub)) as [v |] eqn:Hlast; [| contradiction].
      destruct (PipeHolds_last m (S k) sub ys v Hys Hlast) as [y [ys' [-> _]]].
      unfold slotHolds in Hsl; destruct (fifoVal f0) as [w |] eqn:Hf0.
      + destruct Hsl as [z [Hz Hw]]; cbn in Hz; injection Hz as Hxy Hrest; subst x rest.
        exists ys'; split; [apply (IH (S k) sub y ys' f' Hys); [rewrite Hlast; discriminate | exact Hf] |].
        unfold slotHolds; rewrite Hf0; exists z; split; [reflexivity | exact Hw].
      + injection Hsl as Hxy Hrest; subst x rest.
        exists ys'; split; [apply (IH (S k) sub y ys' f' Hys); [rewrite Hlast; discriminate | exact Hf] |].
        unfold slotHolds; rewrite Hf0; reflexivity.
  Qed.

  (* --- The actions --- *)

  Lemma evalActionPropGen_pipeCanEnq : forall {env : Env (stagesTree num_stages)} (s : TreeState ElemState (stagesTree num_stages)) Q,
    evalActionPropGen env (stagedPipeCanEnq StateK num_stages type) s Q <->
    Q s (negb (Zmod.eqb (fifo1_size s.(Fst)) (Zmod.of_Z 2 1))).
  Proof.
    intros env [f rest] Q; unfold stagedPipeCanEnq, stagedPipeTree, stagedStagesTree.
    cbn [evalActionPropGen]; rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_isFull.
    reflexivity.
  Qed.

  Lemma pipeCanEnq_empty : forall (f : TreeState ElemState (fifoTree 1 StateK)),
    negb (Zmod.eqb (fifo1_size f) (Zmod.of_Z 2 1)) = true -> fifoVal f = None.
  Proof.
    intros f H; apply fifoVal_empty.
    destruct (bits1_cases (fifo1_size f)) as [Hs | Hs]; [exact Hs | rewrite Hs in H; discriminate].
  Qed.

  Lemma pipeEnq_fwd : forall {env : Env (stagesTree num_stages)} (s : TreeState ElemState (stagesTree num_stages)) xs x Q,
    PipeHolds 0 num_stages s xs -> fifoVal s.(Fst) = None ->
    evalActionPropGen env (stagedPipeEnq InpK StateK num_stages initFn type x) s Q ->
    exists s', Q s' Zmod.zero /\ PipeHolds 0 num_stages s' (xs ++ [x]).
  Proof.
    intros env s xs x Q Hh Hn.
    pose proof (fifoVal_None_size _ Hn) as Hsz.
    destruct s as [f rest]; unfold stagedPipeEnq, stagedPipeTree, stagedStagesTree in *.
    cbn [evalActionPropGen Fst] in *.
    rewrite evalActionPropGen_toAction, evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_enq, Hsz.
    cbn [negb]; change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false; cbn [negb].
    intros HQ; eexists; split; [exact HQ |].
    apply (PipeHolds_fill_head 0 num_stages (f ,, rest) xs x _ Hh Hn).
    reflexivity.
  Qed.

  Lemma pipeStepAdjacent_fwd : forall m k {env : Env (stagesTree (S m))} (s : TreeState ElemState (stagesTree (S m))) xs Q,
    PipeHolds k (S m) s xs ->
    evalActionPropGen env (stagedPipeStepAdjacent StateK stepFn type m) s Q ->
    exists s', Q s' Zmod.zero /\ PipeHolds k (S m) s' xs.
  Proof.
    intros m k env [f [[g subrest] []]] xs Q Hh.
    unfold stagedPipeStepAdjacent, stagedStagesTree; cbn [stagedStagesTail evalActionPropGen].
    rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_first.
    rewrite evalActionPropGen_liftAction_child1Path, evalActionPropGen_liftAction_child0Path,
      evalActionPropGen_fifo_isFull.
    cbn [PipeHolds Fst Snd] in Hh; destruct Hh as [ys [Hys Hsl]].
    destruct (bits1_cases (fifo1_size f)) as [Hf | Hf]; rewrite Hf.
    - (* the current slot is empty: nothing moves *)
      change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 0)) with true; cbn [evalActionPropGen].
      rewrite evalExpr_And2_Not;
        match goal with |- context [andb (evalExpr ?e) _] => change (evalExpr e) with false end.
      cbn [andb evalActionPropGen]; intros HQ; eexists; split; [exact HQ |].
      exists ys; split; [exact Hys | exact Hsl].
    - change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [evalActionPropGen].
      rewrite evalExpr_And2_Not;
        match goal with |- context [andb (evalExpr ?e) _] => change (evalExpr e) with true end.
      destruct (bits1_cases (fifo1_size g)) as [Hg | Hg]; rewrite Hg.
      + change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false.
        change (evalExpr (Var type Bool false)) with false; cbn [negb andb evalActionPropGen].
        match goal with
        | |- context [evalExpr (ReadStruct (Var type ?K (evalExpr (mkSome (Const type StateK (fifo1_elem f))))) ?i)] =>
            change (evalExpr (ReadStruct (Var type K (evalExpr (mkSome (Const type StateK (fifo1_elem f))))) i)) with (fifo1_elem f)
        end.
        rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
        rewrite evalActionPropGen_liftAction_child1Path, evalActionPropGen_liftAction_child0Path,
          evalActionPropGen_fifo_enq, Hg.
        change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 1)) with false; cbn [negb evalActionPropGen].
        rewrite evalActionPropGen_liftAction_child0Path, evalActionPropGen_fifo_deq, Hf.
        change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [negb evalActionPropGen].
        intros HQ; eexists; split; [exact HQ |].
        unfold slotHolds in Hsl; rewrite (fifoVal_full f Hf) in Hsl; destruct Hsl as [x [-> Hx]].
        exists (ys ++ [x]); split.
        * apply (PipeHolds_fill_head (S k) m (g ,, subrest) ys x _ Hys (fifoVal_empty g Hg)).
          cbn [StageValAt]; rewrite <- Hx; reflexivity.
        * unfold slotHolds; rewrite fifoVal_empty by reflexivity; reflexivity.
      + change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 1)) with true.
        change (evalExpr (Var type Bool true)) with true; cbn [negb andb evalActionPropGen].
        intros HQ; eexists; split; [exact HQ |].
        exists ys; split; [exact Hys | exact Hsl].
  Qed.

  Lemma pipeRules_fwd : forall n k {env : Env (stagesTree n)} r (s : TreeState ElemState (stagesTree n)) xs Q,
    In r (stagedPipeStageRulesChain StateK stepFn type n) ->
    PipeHolds k n s xs ->
    evalActionPropGen env r s Q ->
    exists s', Q s' Zmod.zero /\ PipeHolds k n s' xs.
  Proof.
    induction n as [| m IH]; intros k env r s xs Q Hin Hh; cbn [stagedPipeStageRulesChain] in Hin.
    - destruct Hin.
    - destruct Hin as [<- | Hin]; [apply pipeStepAdjacent_fwd; exact Hh |].
      apply in_map_iff in Hin; destruct Hin as [r' [<- Hin]].
      destruct s as [f [sub []]].
      unfold stagedStagesTree at 1; cbn [stagedStagesTail].
      rewrite evalActionPropGen_liftAction_child1Path; intros Hr.
      cbn [PipeHolds Fst Snd] in Hh; destruct Hh as [ys [Hys Hsl]].
      destruct (IH (S k) _ r' sub ys _ Hin Hys Hr) as [sub' [HQ Hys']].
      eexists; split; [exact HQ |].
      exists ys; split; [exact Hys' | exact Hsl].
  Qed.

  (* `first`: when valid, the spec value of the oldest item; `deq` is then legal. *)
  Definition PipeReady (s : TreeState ElemState (stagesTree num_stages)) : Prop :=
    fifoVal (stagedLastFifo StateK num_stages s) <> None.

  Lemma pipeFirst_fwd : forall {env : Env (stagesTree num_stages)} (s : TreeState ElemState (stagesTree num_stages)) xs Q,
    PipeHolds 0 num_stages s xs ->
    evalActionPropGen env (stagedPipeFirst StateK OutK num_stages finishFn type) s Q ->
    exists o, Q s o /\
      (o @% "valid" = true ->
       exists x rest, xs = x :: rest /\ o @% "data" = evalLetExpr (finishFn type (SV num_stages x)) /\ PipeReady s).
  Proof.
    intros env s xs Q Hh.
    unfold stagedPipeFirst, stagedPipeTree; cbn [evalActionPropGen].
    rewrite evalActionPropGen_stagedLiftLastStage, evalActionPropGen_fifo_first; cbn [evalActionPropGen].
    rewrite evalActionPropGen_toAction; cbn [evalActionPropGen].
    rewrite stagedUpdate_last_id.
    intros HQ; eexists; split; [exact HQ |].
    set (fl := stagedLastFifo StateK num_stages s) in *.
    destruct (bits1_cases (fifo1_size fl)) as [Hs | Hs]; rewrite Hs.
    - change (Zmod.eqb (Zmod.of_Z 2 0) (Zmod.of_Z 2 0)) with true; cbn; discriminate.
    - change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; intros _.
      destruct (PipeHolds_last num_stages 0 s xs (fifo1_elem fl) Hh (fifoVal_full fl Hs)) as [x [rest [-> Hx]]].
      exists x, rest; split; [reflexivity |]; split.
      + cbn [Nat.add] in Hx; rewrite <- Hx; reflexivity.
      + unfold PipeReady; fold fl; rewrite (fifoVal_full fl Hs); discriminate.
  Qed.

  Lemma pipeDeq_fwd : forall {env : Env (stagesTree num_stages)} (s : TreeState ElemState (stagesTree num_stages)) x rest Q,
    PipeHolds 0 num_stages s (x :: rest) -> PipeReady s ->
    evalActionPropGen env (stagedPipeDeq StateK num_stages type) s Q ->
    exists s', Q s' Zmod.zero /\ PipeHolds 0 num_stages s' rest.
  Proof.
    intros env s x rest Q Hh Hr.
    unfold stagedPipeDeq, stagedPipeTree.
    rewrite evalActionPropGen_stagedLiftLastStage, evalActionPropGen_fifo_deq.
    unfold PipeReady in Hr.
    set (fl := stagedLastFifo StateK num_stages s) in *.
    destruct (bits1_cases (fifo1_size fl)) as [Hs | Hs];
      [rewrite (fifoVal_empty fl Hs) in Hr; contradiction |].
    rewrite Hs; change (Zmod.eqb (Zmod.of_Z 2 1) (Zmod.of_Z 2 0)) with false; cbn [negb].
    intros HQ; eexists; split; [exact HQ |].
    apply (PipeHolds_drop_last num_stages 0 s x rest _ Hh Hr).
    reflexivity.
  Qed.

  (* The initial state holds nothing. *)
  Lemma PipeHolds_init : forall n k (s : TreeState ElemState (stagesTree n)),
    InitStateConsistent (stagesTree n) s -> PipeHolds k n s [].
  Proof.
    induction n as [| m IH]; intros k s Hi.
    - destruct s as [f []]; cbn [PipeHolds Fst].
      unfold stagedStagesTree in Hi; cbn in Hi.
      destruct f as [es [sz []]]; destruct Hi as [[_ [Hsz _]] _].
      unfold slotHolds; rewrite fifoVal_empty; [reflexivity |].
      unfold fifo1_size; cbn [Fst Snd] in *; rewrite Hsz; reflexivity.
    - destruct s as [f [sub []]]; cbn [PipeHolds Fst Snd].
      unfold stagedStagesTree in Hi; cbn [stagedStagesTail InitStateConsistent] in Hi.
      destruct Hi as [Hf [Hsub _]].
      exists []; split; [apply IH; exact Hsub |].
      destruct f as [es [sz []]]; cbn in Hf; destruct Hf as [_ [Hsz _]].
      unfold slotHolds; rewrite fifoVal_empty; [reflexivity |].
      unfold fifo1_size; cbn [Fst Snd] in *; rewrite Hsz; reflexivity.
  Qed.
End PipeQueue.

(* ===========================================================================
 * 3. ITERATIVE CONTROLLER
 * =========================================================================== *)

Section IterQueue.
  Variable InpK StateK OutK : Kind.
  Variable num_stages : nat.
  Local Abbreviation stepsSz := (iterStepsSz num_stages).
  Variable numStepsFn : forall ty, ty InpK -> LetExpr ty (Bit stepsSz).
  Variable initFn     : forall ty, ty InpK -> LetExpr ty StateK.
  Variable stepFn     : forall ty, ty StateK -> LetExpr ty StateK.
  Variable finishFn   : forall ty, ty StateK -> LetExpr ty OutK.

  Local Abbreviation iterTree := (stagedIterTree StateK num_stages).
  Local Abbreviation SV := (StageValAt initFn stepFn).
  Local Abbreviation T := (IterTargetSteps InpK num_stages numStepsFn).
  Local Abbreviation At := (IterStateAtStep InpK StateK num_stages numStepsFn initFn stepFn).

  Definition IterHolds (s : TreeState ElemState iterTree) (xs : list (type InpK)) : Prop :=
    (s @% "busy" = false /\ xs = []) \/ (exists x m, xs = [x] /\ At x m s).

  Definition IterReady (s : TreeState ElemState iterTree) : Prop :=
    s @% "busy" = true /\ Zmod.eqb (s @% "stepsRem") (Zmod.of_Z (2 ^ stepsSz) 0) = true.

  Lemma evalActionPropGen_iterCanEnq : forall {env : Env iterTree} (s : TreeState ElemState iterTree) Q,
    evalActionPropGen env (stagedIterCanEnq StateK num_stages type) s Q <-> Q s (negb (s @% "busy")).
  Proof. intros env [busy [stepsRem [st []]]] Q; reflexivity. Qed.

  Lemma iterEnq_fwd : forall {env : Env iterTree} (s : TreeState ElemState iterTree) xs x Q,
    IterHolds s xs -> s @% "busy" = false ->
    evalActionPropGen env (stagedIterEnq InpK StateK num_stages numStepsFn initFn type x) s Q ->
    exists s', Q s' Zmod.zero /\ IterHolds s' (xs ++ [x]).
  Proof.
    intros env s xs x Q Hh Hb Hev.
    assert (Hxs : xs = []).
    { destruct Hh as [[_ ->] | [y [m [_ [Hb' _]]]]]; [reflexivity | rewrite Hb in Hb'; discriminate]. }
    subst xs.
    destruct (evalActionPropGen_to_SemAction _ s Q Hev) as [s' [r [Hsem HQ]]].
    pose proof (Iter_Enq_Step0 InpK StateK num_stages numStepsFn initFn stepFn x s s' r Hb Hsem) as Hat.
    rewrite (bits0_eq r Zmod.zero) in HQ; eexists; split; [exact HQ |].
    right; exists x, 0%nat; split; [reflexivity | exact Hat].
  Qed.

  Lemma iterStep_fwd : forall {env : Env iterTree} (s : TreeState ElemState iterTree) xs Q,
    IterHolds s xs ->
    evalActionPropGen env (stagedIterStep StateK num_stages stepFn type) s Q ->
    exists s', Q s' Zmod.zero /\ IterHolds s' xs.
  Proof.
    intros env s xs Q Hh Hev.
    destruct (evalActionPropGen_to_SemAction _ s Q Hev) as [s' [r [Hsem HQ]]].
    rewrite (bits0_eq r Zmod.zero) in HQ, Hsem.
    eexists; split; [exact HQ |].
    destruct Hh as [[Hb ->] | [x [m [-> Hat]]]].
    - (* idle: nothing happens *)
      pose proof (InversionActionPropGen Hsem) as Hinv.
      destruct s as [busy [stepsRem [st []]]]; cbn in Hb; subst busy.
      unfold stagedIterStep, stagedWorkRegPath, stagedIterTree in Hinv.
      revert Hinv; cbn -[toAction Sub stepsSz]; intros [<- _].
      left; split; reflexivity.
    - destruct (Nat.lt_ge_cases m (T x)) as [Hlt | Hge].
      + right; exists x, (S m); split; [reflexivity |].
        exact (Iter_Step_Inductive InpK StateK num_stages numStepsFn initFn stepFn x m s s' Zmod.zero Hat Hlt Hsem).
      + (* finished: nothing happens *)
        assert (Hm : m = T x) by (destruct Hat as [_ [Hle _]]; lia); subst m.
        pose proof (InversionActionPropGen Hsem) as Hinv.
        destruct s as [busy [stepsRem [st []]]].
        destruct Hat as [Hb [_ [Hrem Hst]]]; cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hb, Hrem, Hst.
        assert (Hsz_pos : 0 < stepsSz) by apply iterStepsSz_pos.
        assert (Hz : Zmod.eqb stepsRem 0%Zmod = true).
        { destruct (Zmod.eqb_spec stepsRem 0%Zmod) as [_ | Hnz]; [reflexivity |].
          exfalso; apply Hnz, Zmod.unsigned_inj.
          pose proof (bits.unsigned_range stepsRem ltac:(lia)).
          rewrite Zmod.unsigned_0; lia. }
        unfold stagedIterStep, stagedWorkRegPath, stagedIterTree in Hinv.
        revert Hinv; cbn -[toAction Sub stepsSz].
        change (negb (Zmod.eqb stepsRem (Zmod.of_Z (2 ^ stepsSz) 0))) with (negb (Zmod.eqb stepsRem 0%Zmod)).
        rewrite Hz, andb_false_r; cbn -[toAction Sub stepsSz]; intros [<- _].
        right; exists x, (T x); split; [reflexivity |].
        split; [exact Hb | split; [lia | split; [exact Hrem | exact Hst]]].
  Qed.

  Lemma iterFirst_fwd : forall {env : Env iterTree} (s : TreeState ElemState iterTree) xs Q,
    IterHolds s xs ->
    evalActionPropGen env (stagedIterFirst StateK OutK num_stages finishFn type) s Q ->
    exists o, Q s o /\
      (o @% "valid" = true ->
       exists x, xs = [x] /\ o @% "data" = evalLetExpr (finishFn type (SV (T x) x)) /\ IterReady s).
  Proof.
    intros env s xs Q Hh.
    destruct s as [busy [stepsRem [st []]]].
    unfold stagedIterFirst, stagedWorkRegPath, stagedIterTree.
    cbn -[toAction mkSome mkNone stepsSz].
    rewrite evalActionPropGen_toAction; cbn -[mkSome mkNone stepsSz].
    intros HQ; eexists; split; [exact HQ |].
    destruct busy; [| cbn; discriminate].
    match goal with |- context [Zmod.eqb stepsRem ?z] => destruct (Zmod.eqb stepsRem z) eqn:Hz end;
      [| cbn; discriminate].
    intros _.
    destruct Hh as [[Hb _] | [x [m [-> Hat]]]]; [cbn in Hb; discriminate |].
    destruct Hat as [_ [Hle [Hrem Hst]]]; cbn [Fst Snd readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst snd eqb readDiffTuple finNum] in Hrem, Hst.
    assert (Hu : Zmod.unsigned stepsRem = 0) by (apply Zmod.eqb_eq in Hz; rewrite Hz; apply Zmod.unsigned_0).
    rewrite Hu in Hrem.
    assert (Hm : m = T x) by lia; subst m.
    exists x; split; [reflexivity | split].
    - cbn; rewrite <- Hst; reflexivity.
    - split; [reflexivity | exact Hz].
  Qed.

  Lemma iterDeq_fwd : forall {env : Env iterTree} (s : TreeState ElemState iterTree) x Q,
    IterHolds s [x] -> IterReady s ->
    evalActionPropGen env (stagedIterDeq StateK num_stages type) s Q ->
    exists s', Q s' Zmod.zero /\ IterHolds s' [].
  Proof.
    intros env s x Q Hh [Hb Hz].
    destruct s as [busy [stepsRem [st []]]]; cbn in Hb, Hz; subst busy.
    unfold stagedIterDeq, stagedWorkRegPath, stagedIterTree.
    cbn -[stepsSz].
    match goal with |- context [Zmod.eqb stepsRem ?z] => replace (Zmod.eqb stepsRem z) with true by (symmetry; exact Hz) end.
    cbn -[stepsSz].
    intros HQ; eexists; split; [exact HQ |].
    left; split; reflexivity.
  Qed.

  Lemma IterHolds_init : forall (s : TreeState ElemState iterTree),
    InitStateConsistent iterTree s -> IterHolds s [].
  Proof.
    intros s Hi; cbn in Hi; subst s; left; split; reflexivity.
  Qed.
End IterQueue.
