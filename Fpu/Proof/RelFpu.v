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
 * The relation behind the FPU interface contract (`RelFpu.v`; the contract is `FpuContract.v`).
 *
 * The ghost `g` lists, in program (issue) order, the operations the impl has accepted since a
 * base spec state `sigma`:
 *   `EExec x i done`   an FP instruction with fu input `x` (operands read at issue), fu `i`;
 *                      `done` once its result has left the fu;
 *   `ELoad rd ov`      an FP load to `rd` (`ov = None` until the data arrives);
 *   `EWrite rd v`, `EFrm v`, `EFflags v`, `EFcsr v`, `EFs v`   writes.
 * `entrySem e s` is the spec effect of `e`; `tau = foldSem g sigma` replays the whole ghost: it
 * is the spec state with every accepted operation applied.
 *
 * `RelC g A p lp ib Ls sigma` (impl arch state `A`, scoreboard `p` / `lp` / `ib`, fus `Ls`):
 * - every recorded operand is what the spec would read at that point (`Cons`);
 * - impl registers that are not busy equal `tau`'s; `frm`, `fs` equal `tau`'s; `fflags` of `tau`
 *   is the impl's ORed with the flags of the pending operations;
 * - `pend` / `lpend` / `intBusy` are exactly the pending FP writers / loads / integer operations;
 * - fu `i` holds the pending operations routed to it, oldest first;
 * - a pending writer of `r` is followed by no write or read of `r` (`NLT`).
 *
 * The preservation lemmas `relC_*` say how each interface action and internal rule extends or
 * updates the ghost.
 *)

From Stdlib Require Import String List ZArith Zmod Zmod.Bits Lia Bool Arith.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Fpu Require Import FpUtil FpCore FpuArch SpecFpu FpuFU ImplFpu.
From Fpu Require Import FpuArchLemmas SpecFpuLemmas FpuFUProof BitVecLemmas ImplFpuLemmas.

Unset Implicit Arguments.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.
Local Open Scope list_scope.

Lemma Zmod_eqb_neq : forall m (a b : Zmod m), a <> b -> Zmod.eqb a b = false.
Proof. intros m a b H; destruct (Zmod.eqb_spec a b); [contradiction | reflexivity]. Qed.

Section RelFpu.
  Variable F : FpFmt.
  Variable xlen wlen : Z.
  Local Abbreviation flen := (fmtW F).
  Variable narrow : list FpFmt.

  Local Abbreviation InK := (FUInK F xlen narrow).
  Local Abbreviation St := (ArchSt flen).

  (* ===========================================================================
   * 1. GHOST ENTRIES AND THEIR SEMANTICS
   * =========================================================================== *)

  Inductive Entry :=
  | EExec (x : type InK) (fu : nat) (done : bool)
  | ELoad (rd : bits FprIdxSz) (ov : option (bits flen))
  | EWrite (rd : bits FprIdxSz) (v : bits flen)
  | EFrm (v : bits 3)
  | EFflags (v : bits 5)
  | EFcsr (v : bits 8)
  | EFs (v : bits 2).

  Definition resOf (x : type InK) : type (FpuResK F xlen) := (fuSpec F xlen wlen narrow x) @% "res".
  Definition rdOf (x : type InK) : bits FprIdxSz := pktRd (x @% "pkt").
  Definition wfX (x : type InK) : bool := (resOf x) @% "writesF".

  Definition entrySem (e : Entry) (s : St) : St :=
    match e with
    | EExec x _ _ => applyRes F xlen s (rdOf x) (resOf x)
    | ELoad rd (Some v) => writeSem F s rd v
    | ELoad _ None => archSetFs flen s dirtyZ
    | EWrite rd v => writeSem F s rd v
    | EFrm v => frmWriteSem F s v
    | EFflags v => fflagsWriteSem F s v
    | EFcsr v => fcsrWriteSem F s v
    | EFs v => fsWriteSem F s v
    end.

  Definition foldSem (g : list Entry) (s : St) : St := fold_left (fun s e => entrySem e s) g s.

  (* The recorded operands are those the spec reads. *)
  Definition entryOk (s : St) (e : Entry) : Prop :=
    match e with
    | EExec x _ _ => x = inpOf F xlen narrow s (x @% "pkt") (x @% "x")
    | _ => True
    end.

  Fixpoint Cons (s : St) (g : list Entry) : Prop :=
    match g with
    | nil => True
    | e :: rest => entryOk s e /\ Cons (entrySem e s) rest
    end.

  (* Pending writers, readers. *)
  Definition pendWE (e : Entry) (r : bits FprIdxSz) : bool :=
    match e with EExec x _ false => wfX x && Zmod.eqb (rdOf x) r | _ => false end.
  Definition pendWL (e : Entry) (r : bits FprIdxSz) : bool :=
    match e with ELoad rd None => Zmod.eqb rd r | _ => false end.
  Definition pendW (e : Entry) (r : bits FprIdxSz) : bool := pendWE e r || pendWL e r.

  Definition writesR (e : Entry) (r : bits FprIdxSz) : bool :=
    match e with
    | EExec x _ _ => wfX x && Zmod.eqb (rdOf x) r
    | ELoad rd _ | EWrite rd _ => Zmod.eqb rd r
    | _ => false
    end.
  Definition readsR (e : Entry) (r : bits FprIdxSz) : bool :=
    match e with
    | EExec x _ _ => Zmod.eqb (pktRs1 (x @% "pkt")) r || Zmod.eqb (pktRs2 (x @% "pkt")) r || Zmod.eqb (pktRs3 (x @% "pkt")) r
    | _ => false
    end.

  Definition cleanFor (r : bits FprIdxSz) (l : list Entry) : Prop :=
    forall e, In e l -> writesR e r = false /\ readsR e r = false.

  (* No later touch: a pending writer of `r` is followed by no write or read of `r`. *)
  Fixpoint NLT (g : list Entry) : Prop :=
    match g with
    | nil => True
    | e :: rest => (forall r, pendW e r = true -> cleanFor r rest) /\ NLT rest
    end.

  Definition isPendInt (e : Entry) : bool :=
    match e with EExec x _ false => negb (wfX x) | _ => false end.

  Definition flagsE (e : Entry) : bits 5 :=
    match e with EExec x _ false => (resOf x) @% "flags" | _ => Zmod.zero end.

  Definition pendFlags (g : list Entry) : bits 5 := fold_right (fun e acc => Zmod.or (flagsE e) acc) Zmod.zero g.

  Definition entryPendIn (i : nat) (e : Entry) : list (type InK) :=
    match e with EExec x j false => if Nat.eqb j i then [x] else [] | _ => [] end.

  Definition pendIn (g : list Entry) (i : nat) : list (type InK) := flat_map (entryPendIn i) g.

  (* ===========================================================================
   * 2. GENERIC GHOST-LIST LEMMAS
   * =========================================================================== *)

  Lemma foldSem_app : forall g1 g2 s, foldSem (g1 ++ g2) s = foldSem g2 (foldSem g1 s).
  Proof. intros; unfold foldSem; apply fold_left_app. Qed.

  Lemma foldSem_snoc : forall g e s, foldSem (g ++ [e]) s = entrySem e (foldSem g s).
  Proof. intros; rewrite foldSem_app; reflexivity. Qed.

  Lemma Cons_app : forall g1 g2 s, Cons s (g1 ++ g2) <-> Cons s g1 /\ Cons (foldSem g1 s) g2.
  Proof.
    induction g1 as [| e g1 IH]; intros g2 s; cbn [app Cons]; [tauto |].
    rewrite IH; unfold foldSem; cbn [fold_left]; tauto.
  Qed.

  Lemma Cons_snoc : forall g e s, Cons s (g ++ [e]) <-> Cons s g /\ entryOk (foldSem g s) e.
  Proof. intros; rewrite Cons_app; cbn [Cons]; tauto. Qed.

  Lemma existsb_app3 : forall (f : Entry -> bool) pre e post,
    existsb f (pre ++ e :: post) = existsb f pre || f e || existsb f post.
  Proof. intros; rewrite existsb_app; cbn [existsb]; apply orb_assoc. Qed.

  Lemma pendFlags_app : forall g1 g2, pendFlags (g1 ++ g2) = Zmod.or (pendFlags g1) (pendFlags g2).
  Proof.
    induction g1 as [| e g1 IH]; intros g2; cbn [app pendFlags fold_right].
    - rewrite bits_or_0_l; reflexivity.
    - fold (pendFlags (g1 ++ g2)) (pendFlags g1); rewrite IH, bits_or_assoc; reflexivity.
  Qed.

  Lemma pendIn_app : forall g1 g2 i, pendIn (g1 ++ g2) i = pendIn g1 i ++ pendIn g2 i.
  Proof. intros; unfold pendIn; apply flat_map_app. Qed.

  Lemma NLT_app : forall g1 g2,
    NLT (g1 ++ g2) <-> NLT g1 /\ NLT g2 /\ (forall e r, In e g1 -> pendW e r = true -> cleanFor r g2).
  Proof.
    induction g1 as [| e g1 IH]; intros g2; cbn [app NLT].
    - split; [intros H; split; [exact I | split; [exact H | intros ? ? []]] | tauto].
    - rewrite IH; split.
      + intros [He [H1 [H2 H3]]]; split; [split; [| exact H1] | split; [exact H2 |]].
        * intros r Hr e' He'; apply (He r Hr); apply in_or_app; left; exact He'.
        * intros e0 r [<- | Hin] Hr e' He'; [apply (He r Hr); apply in_or_app; right; exact He' | exact (H3 e0 r Hin Hr e' He')].
      + intros [[He H1] [H2 H3]]; split; [| split; [exact H1 | split; [exact H2 |]]].
        * intros r Hr e' He'; apply in_app_or in He'; destruct He' as [He' | He'];
            [exact (He r Hr e' He') | exact (H3 e r (or_introl eq_refl) Hr e' He')].
        * intros e0 r Hin Hr; exact (H3 e0 r (or_intror Hin) Hr).
  Qed.

  Lemma length_filter_app : forall (f : Entry -> bool) g1 g2,
    length (filter f (g1 ++ g2)) = (length (filter f g1) + length (filter f g2))%nat.
  Proof. intros; rewrite filter_app, length_app; reflexivity. Qed.

  (* --- How each entry changes the views --- *)

  Lemma archFrm_entrySem : forall e s,
    archFrm flen (entrySem e s) =
    match e with EFrm v => v | EFcsr v => evalExpr (TruncMsb 3 5 (Var type (Bit 8) v)) | _ => archFrm flen s end.
  Proof.
    intros [x i d | rd [v |] | rd v | v | v | v | v] s; cbn [entrySem]; try reflexivity;
      unfold applyRes; destruct ((resOf x) @% "writesF"); reflexivity.
  Qed.

  Lemma archFs_entrySem : forall e s,
    archFs flen (entrySem e s) = match e with EFs v => v | _ => dirtyZ end.
  Proof.
    intros [x i d | rd [v |] | rd v | v | v | v | v] s; cbn [entrySem]; try reflexivity;
      unfold applyRes; destruct ((resOf x) @% "writesF"); reflexivity.
  Qed.

  Lemma archFflags_entrySem : forall e s,
    archFflags flen (entrySem e s) =
    match e with
    | EExec x _ _ => Zmod.or (archFflags flen s) ((resOf x) @% "flags")
    | EFflags v => v
    | EFcsr v => evalExpr (TruncLsb 3 5 (Var type (Bit 8) v))
    | _ => archFflags flen s
    end.
  Proof.
    intros [x i d | rd [v |] | rd v | v | v | v | v] s; cbn [entrySem]; try reflexivity;
      unfold applyRes; destruct ((resOf x) @% "writesF"); reflexivity.
  Qed.

  Lemma archFpr_entrySem_other : forall e s r, writesR e r = false -> archFpr flen (entrySem e s) r = archFpr flen s r.
  Proof.
    intros [x i d | rd [v |] | rd v | v | v | v | v] s r Hw; cbn [entrySem writesR] in *;
      unfold writeSem, frmWriteSem, fflagsWriteSem, fcsrWriteSem, fsWriteSem;
      rewrite ?archFpr_setFs, ?archFpr_setFflags, ?archFpr_setFrm;
      try (apply archFpr_setFpr_other; intros He; subst r; rewrite Zmod.eqb_refl in Hw; discriminate Hw);
      try (match goal with |- ?a = ?a => reflexivity end).
    unfold applyRes, wfX in *; set (rx := resOf x) in *; clearbody rx.
    rewrite archFpr_setFs, archFpr_setFflags; destruct (rx @% "writesF"); [| reflexivity].
    cbn [andb] in Hw; apply archFpr_setFpr_other; intros He; subst r; rewrite Zmod.eqb_refl in Hw; discriminate.
  Qed.

  Lemma archFpr_foldSem_other : forall g s r, (forall e, In e g -> writesR e r = false) ->
    archFpr flen (foldSem g s) r = archFpr flen s r.
  Proof.
    induction g as [| e g IH]; intros s r Hw; [reflexivity |].
    unfold foldSem; cbn [fold_left]; fold (foldSem g (entrySem e s)).
    rewrite IH by (intros e' He'; apply Hw; right; exact He').
    apply archFpr_entrySem_other, Hw; left; reflexivity.
  Qed.

  (* Two states agreeing everywhere except on register `rd`. *)
  Definition agreeExcept (rd : bits FprIdxSz) (s1 s2 : St) : Prop :=
    archFrm flen s1 = archFrm flen s2 /\ archFflags flen s1 = archFflags flen s2 /\ archFs flen s1 = archFs flen s2 /\
    forall r, r <> rd -> archFpr flen s1 r = archFpr flen s2 r.

  Lemma archFpr_setFpr : forall (s : St) i j v,
    archFpr flen (archSetFpr flen s i v) j = if Zmod.eqb j i then v else archFpr flen s j.
  Proof.
    intros s i j v; destruct (Zmod.eqb_spec j i) as [-> | Hne];
      [apply archFpr_setFpr_same | apply archFpr_setFpr_other; exact Hne].
  Qed.

  Lemma agreeExcept_setFpr : forall rd s1 s2 i v, agreeExcept rd s1 s2 ->
    agreeExcept rd (archSetFpr flen s1 i v) (archSetFpr flen s2 i v).
  Proof.
    intros rd s1 s2 i v [H1 [H2 [H3 H4]]]; split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
    intros r Hr; rewrite !archFpr_setFpr; destruct (Zmod.eqb r i); [reflexivity | apply H4; exact Hr].
  Qed.

  Lemma agreeExcept_entrySem : forall rd e s1 s2, agreeExcept rd s1 s2 -> agreeExcept rd (entrySem e s1) (entrySem e s2).
  Proof.
    intros rd e s1 s2 Ha.
    assert (Hfpr : forall r, r <> rd -> archFpr flen (entrySem e s1) r = archFpr flen (entrySem e s2) r).
    { destruct Ha as [_ [_ [_ H4]]].
      destruct e as [x i d | rd' [v |] | rd' v | v | v | v | v]; cbn [entrySem]; intros r Hr;
        unfold writeSem, frmWriteSem, fflagsWriteSem, fcsrWriteSem, fsWriteSem;
        rewrite ?archFpr_setFs, ?archFpr_setFflags, ?archFpr_setFrm, ?archFpr_setFpr;
        try (apply H4; exact Hr).
      1: unfold applyRes; set (rx := resOf x); clearbody rx; rewrite !archFpr_setFs, !archFpr_setFflags;
         destruct (rx @% "writesF"); [rewrite !archFpr_setFpr | apply H4; exact Hr].
      all: destruct (Zmod.eqb r _); [reflexivity | apply H4; exact Hr]. }
    destruct Ha as [H1 [H2 [H3 _]]].
    split; [rewrite !archFrm_entrySem, H1; reflexivity |].
    split; [rewrite !archFflags_entrySem, H2; reflexivity |].
    split; [rewrite !archFs_entrySem; reflexivity | exact Hfpr].
  Qed.

  Lemma agreeExcept_foldSem : forall rd g s1 s2, agreeExcept rd s1 s2 -> agreeExcept rd (foldSem g s1) (foldSem g s2).
  Proof.
    intros rd; induction g as [| e g IH]; intros s1 s2 Ha; [exact Ha |].
    unfold foldSem; cbn [fold_left]; apply IH, agreeExcept_entrySem, Ha.
  Qed.

  Lemma inpOf_agree : forall rd s1 s2 pkt x, agreeExcept rd s1 s2 ->
    pktRs1 pkt <> rd -> pktRs2 pkt <> rd -> pktRs3 pkt <> rd ->
    inpOf F xlen narrow s1 pkt x = inpOf F xlen narrow s2 pkt x.
  Proof.
    intros rd s1 s2 pkt x [H1 [_ [_ H4]]] Hr1 Hr2 Hr3; unfold inpOf.
    rewrite H1, (H4 _ Hr1), (H4 _ Hr2), (H4 _ Hr3); reflexivity.
  Qed.

  Lemma Cons_agree : forall rd g s1 s2, agreeExcept rd s1 s2 ->
    (forall e, In e g -> readsR e rd = false) -> Cons s1 g -> Cons s2 g.
  Proof.
    intros rd; induction g as [| e g IH]; intros s1 s2 Ha Hr Hc; [exact I |].
    destruct Hc as [He Hc]; split.
    - destruct e as [x i d | | | | | |]; try exact I; cbn [entryOk] in *.
      specialize (Hr _ (or_introl eq_refl)); cbn [readsR] in Hr.
      apply orb_false_iff in Hr; destruct Hr as [Hr Hr3]; apply orb_false_iff in Hr; destruct Hr as [Hr1 Hr2].
      rewrite He at 1; apply (inpOf_agree rd); [exact Ha | | |];
        intros Heq; [rewrite Heq, Zmod.eqb_refl in Hr1 | rewrite Heq, Zmod.eqb_refl in Hr2 | rewrite Heq, Zmod.eqb_refl in Hr3];
        discriminate.
    - apply (IH (entrySem e s1)); [apply agreeExcept_entrySem, Ha | intros e' He'; apply Hr; right; exact He' | exact Hc].
  Qed.

  (* ===========================================================================
   * 3. THE RELATION
   * =========================================================================== *)

  Variable lps : list (FUP F xlen narrow).
  Local Abbreviation ls := (map (fuL F xlen narrow) lps).
  Local Abbreviation LsSt := (TreeState ElemState (fusTree F xlen narrow ls)).

  (* FUs accept only operations whose result destination agrees with `wfOf` (true of the
   * standard fus: they accept supported formats only). *)
  Definition FUsWf : Prop :=
    forall p, In p lps -> forall x : type InK, acceptsF F xlen narrow (fuL F xlen narrow p) (x @% "pkt") = true -> wfX x = wfOf (x @% "pkt").

  Record RelC (g : list Entry) (A : St) (p lp : bits RegVecSz) (ib : bool) (Ls : LsSt) (sigma : St) : Prop := {
    r_cons  : Cons sigma g ;
    r_fpr   : forall r, busyF p lp r = false -> archFpr flen A r = archFpr flen (foldSem g sigma) r ;
    r_frm   : archFrm flen A = archFrm flen (foldSem g sigma) ;
    r_fs    : archFs flen A = archFs flen (foldSem g sigma) ;
    r_ff    : archFflags flen (foldSem g sigma) = Zmod.or (archFflags flen A) (pendFlags g) ;
    r_pend  : forall r, bitOf p r = existsb (fun e => pendWE e r) g ;
    r_lpend : forall r, bitOf lp r = existsb (fun e => pendWL e r) g ;
    r_ib    : length (filter isPendInt g) = (if ib then 1 else 0)%nat ;
    r_fus : FUsHold F xlen narrow lps Ls (pendIn g) ;
    r_nlt   : NLT g ;
    r_route : forall x i d, In (EExec x i d) g -> route F xlen narrow lps (x @% "pkt") = Some i
  }.

  (* --- Consequences --- *)

  Lemma existsb_orb : forall (f h : Entry -> bool) l, existsb (fun e => f e || h e) l = existsb f l || existsb h l.
  Proof.
    induction l as [| e l IH]; [reflexivity |]; cbn [existsb]; rewrite IH.
    destruct (f e), (h e), (existsb f l), (existsb h l); reflexivity.
  Qed.

  Lemma busy_existsb : forall g A p lp ib Ls sigma r, RelC g A p lp ib Ls sigma ->
    busyF p lp r = existsb (fun e => pendW e r) g.
  Proof. intros g A p lp ib Ls sigma r H; unfold busyF, pendW; rewrite existsb_orb, (r_pend _ _ _ _ _ _ _ H), (r_lpend _ _ _ _ _ _ _ H); reflexivity. Qed.

  Lemma notbusy_nopend : forall g A p lp ib Ls sigma r, RelC g A p lp ib Ls sigma ->
    busyF p lp r = false -> forall e, In e g -> pendW e r = false.
  Proof.
    intros g A p lp ib Ls sigma r H Hb e He; rewrite (busy_existsb _ _ _ _ _ _ _ r H) in Hb.
    destruct (pendW e r) eqn:Hp; [| reflexivity].
    exfalso; assert (existsb (fun e => pendW e r) g = true) by (apply existsb_exists; exists e; split; assumption).
    congruence.
  Qed.

  Lemma pendWE_writes : forall e r, pendWE e r = true -> writesR e r = true.
  Proof. intros [x i [|] | | | | | |] r H; cbn [pendWE writesR] in *; try discriminate; exact H. Qed.
  Lemma pendWL_writes : forall e r, pendWL e r = true -> writesR e r = true.
  Proof. intros [| rd [v |] | | | | |] r H; cbn [pendWL writesR] in *; try discriminate; exact H. Qed.
  Lemma pendW_writes : forall e r, pendW e r = true -> writesR e r = true.
  Proof. intros e r H; unfold pendW in H; apply orb_true_iff in H; destruct H; [apply pendWE_writes | apply pendWL_writes]; assumption. Qed.

  Lemma route_accepts : forall l pkt i, route F xlen narrow l pkt = Some i ->
    exists p, nth_error l i = Some p /\ acceptsF F xlen narrow (fuL F xlen narrow p) pkt = true.
  Proof.
    induction l as [| q l IH]; intros pkt i H; cbn [route] in H; [discriminate |].
    destruct (acceptsF F xlen narrow (fuL F xlen narrow q) pkt) eqn:Ha.
    - injection H as <-; exists q; split; [reflexivity | exact Ha].
    - destruct (route F xlen narrow l pkt) as [j |] eqn:Hr; [| discriminate].
      injection H as <-; destruct (IH _ _ Hr) as [q' [Hq Haq]]; exists q'; split; [exact Hq | exact Haq].
  Qed.

  Lemma route_wf : FUsWf -> forall (x : type InK) i, route F xlen narrow lps (x @% "pkt") = Some i -> wfX x = wfOf (x @% "pkt").
  Proof.
    intros Hwf x i Hr; destruct (route_accepts _ _ _ Hr) as [q [Hq Ha]].
    apply (Hwf q); [eapply nth_error_In; exact Hq | exact Ha].
  Qed.

  Lemma sbOkF_true : forall p lp ib (pkt : type (FpuPktK narrow)) wf, sbOkF p lp ib pkt wf = true ->
    busyF p lp (pktRs1 pkt) = false /\ busyF p lp (pktRs2 pkt) = false /\ busyF p lp (pktRs3 pkt) = false /\
    (if wf then busyF p lp (pktRd pkt) = false else ib = false).
  Proof.
    intros p lp ib pkt wf H; unfold sbOkF in H.
    repeat (apply andb_true_iff in H; destruct H as [H ?]).
    repeat match goal with Hn : negb _ = true |- _ => apply negb_true_iff in Hn end.
    split; [assumption | split; [assumption | split; [assumption |]]].
    destruct wf; apply negb_true_iff; assumption.
  Qed.

  Lemma bitOf_setV : forall w r j, bitOf (bitSetV w r) j = if Zmod.eqb j r then true else bitOf w j.
  Proof. intros; apply bitOf_set. Qed.
  Lemma bitOf_clrV : forall w r j, bitOf (bitClrV w r) j = if Zmod.eqb j r then false else bitOf w j.
  Proof. intros; apply bitOf_clr. Qed.

  Lemma inpOf_pkt : forall (A : St) pkt (xv : bits xlen), (inpOf F xlen narrow A pkt xv) @% "pkt" = pkt.
  Proof. reflexivity. Qed.

  (* ===========================================================================
   * 4. PRESERVATION: ISSUE
   * =========================================================================== *)

  Lemma relC_issue : forall g A p lp ib Ls sigma pkt (xv : bits xlen) i Ls',
    FUsWf -> RelC g A p lp ib Ls sigma ->
    sbOkF p lp ib pkt (wfOf pkt) = true -> route F xlen narrow lps pkt = Some i ->
    FUsHold F xlen narrow lps Ls' (setAt F xlen narrow (pendIn g) i (pendIn g i ++ [inpOf F xlen narrow A pkt xv])) ->
    RelC (g ++ [EExec (inpOf F xlen narrow A pkt xv) i false]) (archSetFs flen A dirtyZ)
      (if wfOf pkt then bitSetV p (pktRd pkt) else p) lp (if wfOf pkt then ib else true) Ls' sigma.
  Proof.
    intros g A p lp ib Ls sigma pkt xv i Ls' Hwfl H Hsb Hr Hl'.
    set (x := inpOf F xlen narrow A pkt xv) in *.
    set (tau := foldSem g sigma).
    destruct (sbOkF_true _ _ _ _ _ Hsb) as [Hb1 [Hb2 [Hb3 Hrd]]].
    assert (Hwf : wfX x = wfOf pkt) by (apply (route_wf Hwfl x i); exact Hr).
    assert (Hx : x = inpOf F xlen narrow tau pkt xv).
    { unfold x, inpOf; rewrite (r_frm _ _ _ _ _ _ _ H), (r_fpr _ _ _ _ _ _ _ H _ Hb1),
        (r_fpr _ _ _ _ _ _ _ H _ Hb2), (r_fpr _ _ _ _ _ _ _ H _ Hb3); reflexivity. }
    (* pending writers of the sources / destination *)
    assert (Hnp : forall r, busyF p lp r = false -> forall e0, In e0 g -> pendW e0 r = false)
      by (intros r Hb; exact (notbusy_nopend _ _ _ _ _ _ _ r H Hb)).
    constructor.
    - apply Cons_snoc; split; [exact (r_cons _ _ _ _ _ _ _ H) | exact Hx].
    - intros r Hb; rewrite foldSem_snoc; fold tau.
      change (archFpr flen (archSetFs flen A dirtyZ) r) with (archFpr flen A r).
      rewrite archFpr_entrySem_other.
      + apply (r_fpr _ _ _ _ _ _ _ H); unfold busyF in *; destruct (wfOf pkt).
        * rewrite bitOf_setV in Hb; destruct (Zmod.eqb r (pktRd pkt)); [discriminate | exact Hb].
        * exact Hb.
      + cbn [writesR]; rewrite Hwf; destruct (wfOf pkt); [| reflexivity].
        cbn [andb]; unfold busyF in Hb; rewrite bitOf_setV in Hb.
        destruct (Zmod.eqb_spec (rdOf x) r) as [<- | _]; [| reflexivity].
        change (rdOf x) with (pktRd pkt) in Hb; rewrite Zmod.eqb_refl in Hb; discriminate.
    - rewrite foldSem_snoc, archFrm_entrySem; exact (r_frm _ _ _ _ _ _ _ H).
    - rewrite foldSem_snoc, archFs_entrySem; reflexivity.
    - rewrite foldSem_snoc, archFflags_entrySem, (r_ff _ _ _ _ _ _ _ H), pendFlags_app.
      cbn [pendFlags fold_right flagsE]; rewrite bits_or_0_r, bits_or_assoc; reflexivity.
    - intros r; rewrite existsb_app; cbn [existsb pendWE]; rewrite orb_false_r, Hwf.
      destruct (wfOf pkt); cbn [andb]; [| rewrite (r_pend _ _ _ _ _ _ _ H), orb_false_r; reflexivity].
      rewrite bitOf_setV, (r_pend _ _ _ _ _ _ _ H); change (rdOf x) with (pktRd pkt).
      destruct (Zmod.eqb_spec r (pktRd pkt)) as [-> | Hne]; [rewrite Zmod.eqb_refl, orb_true_r; reflexivity |].
      replace (Zmod.eqb (pktRd pkt) r) with false; [rewrite orb_false_r; reflexivity |].
      symmetry; apply Zmod_eqb_neq; intros He; apply Hne; symmetry; exact He.
    - intros r; rewrite existsb_app; cbn [existsb pendWL]; rewrite orb_false_r; exact (r_lpend _ _ _ _ _ _ _ H r).
    - rewrite length_filter_app, (r_ib _ _ _ _ _ _ _ H); cbn [filter isPendInt]; rewrite Hwf.
      destruct (wfOf pkt); cbn [negb length]; [lia |].
      rewrite Hrd; reflexivity.
    - eapply FUsHold_ext; [| exact Hl']; intros j; unfold setAt; rewrite pendIn_app.
      change (pendIn [EExec x i false] j) with (entryPendIn j (EExec x i false) ++ []); cbn [entryPendIn].
      destruct (Nat.eqb_spec j i) as [-> | Hne].
      + rewrite Nat.eqb_refl; reflexivity.
      + rewrite (proj2 (Nat.eqb_neq i j) (fun Hij => Hne (eq_sym Hij))); cbn [app]; rewrite app_nil_r; reflexivity.
    - apply NLT_app; split; [exact (r_nlt _ _ _ _ _ _ _ H) | split; [split; [intros r _ ? [] | exact I] |]].
      intros e0 r He0 Hp e' [<- | []]; split.
      + cbn [writesR]; rewrite Hwf; destruct (wfOf pkt) eqn:Hw; [| reflexivity].
        destruct (Zmod.eqb_spec (rdOf x) r) as [Heq | _]; [| apply andb_false_r].
        change (rdOf x) with (pktRd pkt) in Heq; subst r.
        rewrite (Hnp _ Hrd e0 He0) in Hp; discriminate.
      + cbn [readsR]; change (x @% "pkt") with pkt.
        destruct (Zmod.eqb_spec (pktRs1 pkt) r) as [<- | _]; [rewrite (Hnp _ Hb1 e0 He0) in Hp; discriminate |].
        destruct (Zmod.eqb_spec (pktRs2 pkt) r) as [<- | _]; [rewrite (Hnp _ Hb2 e0 He0) in Hp; discriminate |].
        destruct (Zmod.eqb_spec (pktRs3 pkt) r) as [<- | _]; [rewrite (Hnp _ Hb3 e0 He0) in Hp; discriminate |].
        reflexivity.
    - intros x' i' d Hin; apply in_app_or in Hin; destruct Hin as [Hin | [Heq | []]].
      + exact (r_route _ _ _ _ _ _ _ H _ _ _ Hin).
      + injection Heq as <- <- _; exact Hr.
  Qed.

  (* ===========================================================================
   * 5. PRESERVATION: COMPLETION OF A PENDING OPERATION
   * =========================================================================== *)

  Lemma markDone_split : forall g i x xs, pendIn g i = x :: xs ->
    exists pre post, g = pre ++ EExec x i false :: post /\ pendIn pre i = [] /\ pendIn post i = xs.
  Proof.
    induction g as [| e g IH]; intros i x xs H; [discriminate |].
    unfold pendIn in H; cbn [flat_map] in H; fold (pendIn g i) in H.
    destruct e as [y j [|] | | | | | |]; cbn [entryPendIn app] in H;
      try (destruct (IH _ _ _ H) as [pre [post [-> [Hpre Hpost]]]];
           eexists (_ :: pre), post; split; [reflexivity | split; [exact Hpre | exact Hpost]]).
    destruct (Nat.eqb_spec j i) as [-> | Hne]; cbn [app] in H.
    - injection H as <- <-; exists [], g; split; [reflexivity | split; reflexivity].
    - destruct (IH _ _ _ H) as [pre [post [-> [Hpre Hpost]]]].
      exists (EExec y j false :: pre), post; split; [reflexivity |]; split; [| exact Hpost].
      unfold pendIn; cbn [flat_map entryPendIn]; rewrite (proj2 (Nat.eqb_neq j i) Hne); exact Hpre.
  Qed.

  Lemma existsb_false_intro : forall (f : Entry -> bool) l, (forall e, In e l -> f e = false) -> existsb f l = false.
  Proof.
    intros f l H; induction l as [| e l IH]; [reflexivity |]; cbn [existsb].
    rewrite (H e (or_introl eq_refl)), IH; [reflexivity | intros e' He'; apply H; right; exact He'].
  Qed.

  Lemma or_swap5 : forall (a f P Q : bits 5),
    Zmod.or a (Zmod.or P (Zmod.or f Q)) = Zmod.or (Zmod.or a f) (Zmod.or P (Zmod.or Zmod.zero Q)).
  Proof.
    intros; rewrite bits_or_0_l, !bits_or_assoc; f_equal.
    rewrite <- !bits_or_assoc; f_equal; apply bits_or_comm.
  Qed.

  Lemma relC_mark : forall g A p lp ib Ls sigma pre post x i,
    RelC g A p lp ib Ls sigma -> g = pre ++ EExec x i false :: post -> pendIn pre i = [] ->
    let g' := pre ++ EExec x i true :: post in
    Cons sigma g' /\ foldSem g' sigma = foldSem g sigma /\
    archFflags flen (foldSem g sigma) = Zmod.or (Zmod.or (archFflags flen A) ((resOf x) @% "flags")) (pendFlags g') /\
    (forall r, existsb (fun e => pendWE e r) g = existsb (fun e => pendWE e r) g' || (wfX x && Zmod.eqb (rdOf x) r)) /\
    (forall r, existsb (fun e => pendWL e r) g' = existsb (fun e => pendWL e r) g) /\
    length (filter isPendInt g) = (length (filter isPendInt g') + (if wfX x then 0 else 1))%nat /\
    (forall j, pendIn g' j = setAt F xlen narrow (pendIn g) i (pendIn post i) j) /\
    NLT g' /\
    (forall x' i' d, In (EExec x' i' d) g' -> route F xlen narrow lps (x' @% "pkt") = Some i').
  Proof.
    intros g A p lp ib Ls sigma pre post x i H -> Hpre g'.
    pose proof (r_cons _ _ _ _ _ _ _ H) as Hc; apply Cons_app in Hc; destruct Hc as [Hc1 [He Hc2]].
    split; [apply Cons_app; split; [exact Hc1 | split; [exact He | exact Hc2]] |].
    split; [unfold g'; rewrite !foldSem_app; reflexivity |].
    split.
    { rewrite (r_ff _ _ _ _ _ _ _ H); unfold g'; rewrite !pendFlags_app; cbn [pendFlags fold_right flagsE].
      apply or_swap5. }
    split.
    { intros r; unfold g'; rewrite !existsb_app3; cbn [pendWE]; rewrite orb_false_r.
      destruct (existsb (fun e => pendWE e r) pre), (wfX x && Zmod.eqb (rdOf x) r), (existsb (fun e => pendWE e r) post); reflexivity. }
    split; [intros r; unfold g'; rewrite !existsb_app3; reflexivity |].
    split.
    { unfold g'; rewrite !length_filter_app; cbn [filter isPendInt]; destruct (wfX x); cbn [negb length]; lia. }
    split.
    { intros j; unfold setAt, g'; rewrite !pendIn_app.
      change (pendIn (EExec x i true :: post) j) with (pendIn post j).
      change (pendIn (EExec x i false :: post) j) with (entryPendIn j (EExec x i false) ++ pendIn post j); cbn [entryPendIn].
      destruct (Nat.eqb_spec j i) as [-> | Hne]; [rewrite Hpre; reflexivity |].
      rewrite (proj2 (Nat.eqb_neq i j) (fun Hij => Hne (eq_sym Hij))); reflexivity. }
    split.
    { pose proof (r_nlt _ _ _ _ _ _ _ H) as Hn; apply NLT_app in Hn; destruct Hn as [Hn1 [[_ Hn2] Hn3]].
      apply NLT_app; split; [exact Hn1 | split; [split; [intros r Hr; discriminate | exact Hn2] |]].
      intros e0 r He0 Hp e' [<- | He'];
        [exact (Hn3 e0 r He0 Hp (EExec x i false) (or_introl eq_refl)) | exact (Hn3 e0 r He0 Hp e' (or_intror He'))]. }
    { intros x' i' d Hin; unfold g' in Hin; apply in_app_or in Hin.
      destruct Hin as [Hin | [Heq | Hin]].
      - apply (r_route _ _ _ _ _ _ _ H x' i' d); apply in_or_app; left; exact Hin.
      - injection Heq as <- <- _; apply (r_route _ _ _ _ _ _ _ H x i false); apply in_or_app; right; left; reflexivity.
      - apply (r_route _ _ _ _ _ _ _ H x' i' d); apply in_or_app; right; right; exact Hin. }
  Qed.

  Definition wbArch (A : St) (x : type InK) : St :=
    archSetFflags flen (archSetFpr flen A (rdOf x) ((resOf x) @% "res"))
      (Zmod.or (archFflags flen A) ((resOf x) @% "flags")).

  Lemma pendW_exec_wf : forall x i r, wfX x = true -> pendW (EExec x i false) r = Zmod.eqb (rdOf x) r.
  Proof. intros x i r Hw; unfold pendW; cbn [pendWE pendWL]; rewrite Hw, orb_false_r; reflexivity. Qed.

  Lemma relC_wb : forall g A p lp ib Ls sigma i x xs Ls',
    RelC g A p lp ib Ls sigma -> pendIn g i = x :: xs -> wfX x = true ->
    FUsHold F xlen narrow lps Ls' (setAt F xlen narrow (pendIn g) i xs) ->
    exists pre post, g = pre ++ EExec x i false :: post /\
      RelC (pre ++ EExec x i true :: post) (wbArch A x) (bitClrV p (rdOf x)) lp ib Ls' sigma.
  Proof.
    intros g A p lp ib Ls sigma i x xs Ls' H Hx Hw Hl'.
    destruct (markDone_split _ _ _ _ Hx) as [pre [post [Hg [Hpre Hpost]]]].
    exists pre, post; split; [exact Hg |].
    destruct (relC_mark _ _ _ _ _ _ _ _ _ _ _ H Hg Hpre) as [Hc [Hf [Hff [Hpe [Hpl [Hib [Hpi [Hn Hr]]]]]]]].
    set (g' := pre ++ EExec x i true :: post) in *.
    (* the completed entry is the last writer of its destination *)
    assert (Hn0 := r_nlt _ _ _ _ _ _ _ H); rewrite Hg in Hn0; apply NLT_app in Hn0; destruct Hn0 as [_ [[Hclean _] Hcross]].
    specialize (Hclean (rdOf x) ltac:(rewrite pendW_exec_wf by exact Hw; apply Zmod.eqb_refl)).
    assert (Hlast : archFpr flen (foldSem g sigma) (rdOf x) = (resOf x) @% "res").
    { rewrite Hg, foldSem_app; unfold foldSem at 1; cbn [fold_left]; fold (foldSem post (entrySem (EExec x i false) (foldSem pre sigma))).
      rewrite archFpr_foldSem_other by (intros e He; apply (Hclean e He)).
      cbn [entrySem]; unfold applyRes, wfX in *; rewrite Hw.
      apply archFpr_setFpr_same. }
    (* no other pending writer of the destination *)
    assert (Hnone : existsb (fun e => pendWE e (rdOf x)) g' = false).
    { unfold g'; rewrite existsb_app3; cbn [pendWE]; rewrite orb_false_r.
      apply orb_false_iff; split; apply existsb_false_intro; intros e He; destruct (pendWE e (rdOf x)) eqn:Hp; try reflexivity; exfalso.
      - assert (Hpw : pendW e (rdOf x) = true) by (unfold pendW; rewrite Hp; reflexivity).
        destruct (Hcross e (rdOf x) He Hpw (EExec x i false) (or_introl eq_refl)) as [Hwr _].
        cbn [writesR] in Hwr; rewrite Hw, Zmod.eqb_refl in Hwr; discriminate.
      - destruct (Hclean e He) as [Hwr _]; rewrite (pendWE_writes _ _ Hp) in Hwr; discriminate. }
    constructor.
    - exact Hc.
    - intros r Hb; rewrite Hf; unfold wbArch.
      change (archFpr flen (archSetFflags flen (archSetFpr flen A (rdOf x) ((resOf x) @% "res")) (Zmod.or (archFflags flen A) ((resOf x) @% "flags"))) r)
        with (archFpr flen (archSetFpr flen A (rdOf x) ((resOf x) @% "res")) r).
      rewrite archFpr_setFpr; destruct (Zmod.eqb_spec r (rdOf x)) as [-> | Hne]; [symmetry; exact Hlast |].
      apply (r_fpr _ _ _ _ _ _ _ H); unfold busyF in *; rewrite bitOf_clrV in Hb.
      rewrite (Zmod_eqb_neq _ _ _ Hne) in Hb; exact Hb.
    - rewrite Hf; exact (r_frm _ _ _ _ _ _ _ H).
    - rewrite Hf; exact (r_fs _ _ _ _ _ _ _ H).
    - rewrite Hf, Hff; reflexivity.
    - intros r; rewrite bitOf_clrV; destruct (Zmod.eqb_spec r (rdOf x)) as [-> | Hne]; [symmetry; exact Hnone |].
      rewrite (r_pend _ _ _ _ _ _ _ H), Hpe.
      replace (Zmod.eqb (rdOf x) r) with false by (symmetry; apply Zmod_eqb_neq; intros He; apply Hne; symmetry; exact He).
      rewrite andb_false_r, orb_false_r; reflexivity.
    - intros r; rewrite Hpl; exact (r_lpend _ _ _ _ _ _ _ H r).
    - pose proof (r_ib _ _ _ _ _ _ _ H) as Hi; rewrite Hib, Hw in Hi; rewrite <- Hi; lia.
    - eapply FUsHold_ext; [| exact Hl']; intros j; rewrite Hpi, Hpost; reflexivity.
    - exact Hn.
    - exact Hr.
  Qed.

  Lemma relC_intResp : forall g A p lp ib Ls sigma i x xs Ls',
    RelC g A p lp ib Ls sigma -> pendIn g i = x :: xs -> wfX x = false ->
    FUsHold F xlen narrow lps Ls' (setAt F xlen narrow (pendIn g) i xs) ->
    exists pre post, g = pre ++ EExec x i false :: post /\
      RelC (pre ++ EExec x i true :: post) (archSetFflags flen A (Zmod.or (archFflags flen A) ((resOf x) @% "flags")))
        p lp false Ls' sigma.
  Proof.
    intros g A p lp ib Ls sigma i x xs Ls' H Hx Hw Hl'.
    destruct (markDone_split _ _ _ _ Hx) as [pre [post [Hg [Hpre Hpost]]]].
    exists pre, post; split; [exact Hg |].
    destruct (relC_mark _ _ _ _ _ _ _ _ _ _ _ H Hg Hpre) as [Hc [Hf [Hff [Hpe [Hpl [Hib [Hpi [Hn Hr]]]]]]]].
    constructor.
    - exact Hc.
    - intros r Hb; rewrite Hf; exact (r_fpr _ _ _ _ _ _ _ H r Hb).
    - rewrite Hf; exact (r_frm _ _ _ _ _ _ _ H).
    - rewrite Hf; exact (r_fs _ _ _ _ _ _ _ H).
    - rewrite Hf, Hff; reflexivity.
    - intros r; rewrite (r_pend _ _ _ _ _ _ _ H), Hpe, Hw; cbn [andb]; apply orb_false_r.
    - intros r; rewrite Hpl; exact (r_lpend _ _ _ _ _ _ _ H r).
    - pose proof (r_ib _ _ _ _ _ _ _ H) as Hi; rewrite Hib, Hw in Hi; destruct ib; cbn in Hi |- *; lia.
    - eapply FUsHold_ext; [| exact Hl']; intros j; rewrite Hpi, Hpost; reflexivity.
    - exact Hn.
    - exact Hr.
  Qed.

  Lemma relC_fus : forall g A p lp ib Ls Ls' sigma,
    RelC g A p lp ib Ls sigma -> FUsHold F xlen narrow lps Ls' (pendIn g) -> RelC g A p lp ib Ls' sigma.
  Proof. intros g A p lp ib Ls Ls' sigma [? ? ? ? ? ? ? ? ? ? ?] Hl; constructor; assumption. Qed.

  (* ===========================================================================
   * 6. PRESERVATION: WRITES, LOADS
   * =========================================================================== *)

  Lemma relC_snoc_done : forall g A p lp ib Ls sigma e A',
    RelC g A p lp ib Ls sigma ->
    entryOk (foldSem g sigma) e -> isPendInt e = false -> flagsE e = Zmod.zero ->
    (forall r, pendWE e r = false) -> (forall r, pendWL e r = false) -> (forall j, entryPendIn j e = []) ->
    (forall x i d, e <> EExec x i d) ->
    (forall r, busyF p lp r = true -> writesR e r = false /\ readsR e r = false) ->
    (forall r, busyF p lp r = false -> archFpr flen A' r = archFpr flen (entrySem e (foldSem g sigma)) r) ->
    archFrm flen A' = archFrm flen (entrySem e (foldSem g sigma)) ->
    archFs flen A' = archFs flen (entrySem e (foldSem g sigma)) ->
    archFflags flen (entrySem e (foldSem g sigma)) = Zmod.or (archFflags flen A') (pendFlags g) ->
    RelC (g ++ [e]) A' p lp ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma e A' H Hok Hi Hf Hwe Hwl Hpi Hne Hcl Hfpr Hfrm Hfs Hff.
    constructor.
    - apply Cons_snoc; split; [exact (r_cons _ _ _ _ _ _ _ H) | exact Hok].
    - intros r Hb; rewrite foldSem_snoc; exact (Hfpr r Hb).
    - rewrite foldSem_snoc; exact Hfrm.
    - rewrite foldSem_snoc; exact Hfs.
    - rewrite foldSem_snoc, Hff, pendFlags_app; cbn [pendFlags fold_right]; rewrite Hf, bits_or_0_l, bits_or_0_r; reflexivity.
    - intros r; rewrite existsb_app; cbn [existsb]; rewrite Hwe, orb_false_r; exact (r_pend _ _ _ _ _ _ _ H r).
    - intros r; rewrite existsb_app; cbn [existsb]; rewrite Hwl, orb_false_r; exact (r_lpend _ _ _ _ _ _ _ H r).
    - rewrite length_filter_app; cbn [filter]; rewrite Hi; cbn [length]; rewrite Nat.add_0_r; exact (r_ib _ _ _ _ _ _ _ H).
    - eapply FUsHold_ext; [| exact (r_fus _ _ _ _ _ _ _ H)]; intros j; rewrite pendIn_app.
      change (pendIn [e] j) with (entryPendIn j e ++ []); rewrite Hpi; cbn [app]; rewrite app_nil_r; reflexivity.
    - apply NLT_app; split; [exact (r_nlt _ _ _ _ _ _ _ H) | split; [split; [intros r Hr; unfold pendW in Hr; rewrite Hwe, Hwl in Hr; discriminate | exact I] |]].
      intros e0 r He0 Hp e' [<- | []].
      apply Hcl; rewrite (busy_existsb _ _ _ _ _ _ _ r H); apply existsb_exists; exists e0; split; assumption.
    - intros x i d Hin; apply in_app_or in Hin; destruct Hin as [Hin | [Heq | []]];
        [exact (r_route _ _ _ _ _ _ _ H _ _ _ Hin) | exfalso; apply (Hne x i d); exact Heq].
  Qed.

  Lemma relC_writeT : forall g A p lp ib Ls sigma idx v,
    RelC g A p lp ib Ls sigma -> busyF p lp idx = false ->
    RelC (g ++ [EWrite idx v]) (writeSem F A idx v) p lp ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma idx v H Hb.
    apply (relC_snoc_done _ _ _ _ _ _ _ _ _ H); try (intros; exact I); try reflexivity; try discriminate.
    - intros r Hr; split; [cbn [writesR]; apply Zmod_eqb_neq; intros <-; congruence | reflexivity].
    - intros r Hr; cbn [entrySem]; unfold writeSem.
      change (archFpr flen (archSetFpr flen A idx v) r = archFpr flen (archSetFpr flen (foldSem g sigma) idx v) r).
      rewrite !archFpr_setFpr; destruct (Zmod.eqb r idx); [reflexivity | exact (r_fpr _ _ _ _ _ _ _ H r Hr)].
    - exact (r_frm _ _ _ _ _ _ _ H).
    - exact (r_ff _ _ _ _ _ _ _ H).
  Qed.

  Lemma relC_frm : forall g A p lp ib Ls sigma v,
    RelC g A p lp ib Ls sigma -> RelC (g ++ [EFrm v]) (frmWriteSem F A v) p lp ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma v H.
    apply (relC_snoc_done _ _ _ _ _ _ _ _ _ H); try (intros; exact I); try reflexivity; try discriminate.
    - intros r Hr; split; reflexivity.
    - intros r Hr; exact (r_fpr _ _ _ _ _ _ _ H r Hr).
    - exact (r_ff _ _ _ _ _ _ _ H).
  Qed.

  Lemma relC_fs : forall g A p lp ib Ls sigma v,
    RelC g A p lp ib Ls sigma -> RelC (g ++ [EFs v]) (fsWriteSem F A v) p lp ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma v H.
    apply (relC_snoc_done _ _ _ _ _ _ _ _ _ H); try (intros; exact I); try reflexivity; try discriminate.
    - intros r Hr; split; reflexivity.
    - intros r Hr; exact (r_fpr _ _ _ _ _ _ _ H r Hr).
    - exact (r_frm _ _ _ _ _ _ _ H).
    - exact (r_ff _ _ _ _ _ _ _ H).
  Qed.

  (* Nothing in flight: no pending flags. *)
  Lemma pendFlags_zero : forall g, (forall e, In e g -> flagsE e = Zmod.zero) -> pendFlags g = Zmod.zero.
  Proof.
    induction g as [| e g IH]; intros H; [reflexivity |]; cbn [pendFlags fold_right]; fold (pendFlags g).
    rewrite (H e (or_introl eq_refl)), IH by (intros e' He'; apply H; right; exact He'); apply bits_or_0_l.
  Qed.

  Lemma drained_pendFlags : forall g A p lp ib Ls sigma, RelC g A p lp ib Ls sigma ->
    drainedF p ib = true -> pendFlags g = Zmod.zero.
  Proof.
    intros g A p lp ib Ls sigma H Hd; unfold drainedF in Hd; apply andb_true_iff in Hd; destruct Hd as [Hp Hib].
    apply negb_true_iff in Hib; subst ib.
    apply pendFlags_zero; intros [x i [|] | | | | | |] He; try reflexivity; exfalso.
    destruct (wfX x) eqn:Hw.
    - pose proof (r_pend _ _ _ _ _ _ _ H (rdOf x)) as Hpe.
      rewrite (bitOf_zero_eq _ _ Hp) in Hpe; symmetry in Hpe.
      assert (existsb (fun e => pendWE e (rdOf x)) g = true)
        by (apply existsb_exists; exists (EExec x i false); split; [exact He | cbn [pendWE]; rewrite Hw, Zmod.eqb_refl; reflexivity]).
      congruence.
    - pose proof (r_ib _ _ _ _ _ _ _ H) as Hi.
      assert (In (EExec x i false) (filter isPendInt g)) by (apply filter_In; split; [exact He | cbn [isPendInt]; rewrite Hw; reflexivity]).
      destruct (filter isPendInt g); [contradiction | discriminate].
  Qed.

  Lemma relC_fflags : forall g A p lp ib Ls sigma v,
    RelC g A p lp ib Ls sigma -> drainedF p ib = true ->
    RelC (g ++ [EFflags v]) (fflagsWriteSem F A v) p lp ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma v H Hd.
    apply (relC_snoc_done _ _ _ _ _ _ _ _ _ H); try (intros; exact I); try reflexivity; try discriminate.
    - intros r Hr; split; reflexivity.
    - intros r Hr; exact (r_fpr _ _ _ _ _ _ _ H r Hr).
    - exact (r_frm _ _ _ _ _ _ _ H).
    - rewrite (drained_pendFlags _ _ _ _ _ _ _ H Hd), bits_or_0_r; reflexivity.
  Qed.

  Lemma relC_fcsr : forall g A p lp ib Ls sigma v,
    RelC g A p lp ib Ls sigma -> drainedF p ib = true ->
    RelC (g ++ [EFcsr v]) (fcsrWriteSem F A v) p lp ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma v H Hd.
    apply (relC_snoc_done _ _ _ _ _ _ _ _ _ H); try (intros; exact I); try reflexivity; try discriminate.
    - intros r Hr; split; reflexivity.
    - intros r Hr; exact (r_fpr _ _ _ _ _ _ _ H r Hr).
    - rewrite (drained_pendFlags _ _ _ _ _ _ _ H Hd), bits_or_0_r; reflexivity.
  Qed.

  Lemma relC_reserve : forall g A p lp ib Ls sigma rd,
    RelC g A p lp ib Ls sigma -> busyF p lp rd = false ->
    RelC (g ++ [ELoad rd None]) (archSetFs flen A dirtyZ) p (bitSetV lp rd) ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma rd H Hb.
    assert (Hnp := notbusy_nopend _ _ _ _ _ _ _ rd H Hb).
    constructor.
    - apply Cons_snoc; split; [exact (r_cons _ _ _ _ _ _ _ H) | exact I].
    - intros r Hr; rewrite foldSem_snoc; cbn [entrySem].
      change (archFpr flen A r = archFpr flen (foldSem g sigma) r).
      apply (r_fpr _ _ _ _ _ _ _ H); unfold busyF in *; rewrite bitOf_setV in Hr.
      destruct (Zmod.eqb r rd); [rewrite orb_true_r in Hr; discriminate | exact Hr].
    - rewrite foldSem_snoc; exact (r_frm _ _ _ _ _ _ _ H).
    - rewrite foldSem_snoc; reflexivity.
    - rewrite foldSem_snoc, pendFlags_app; cbn [pendFlags fold_right flagsE entrySem].
      rewrite bits_or_0_l, bits_or_0_r; exact (r_ff _ _ _ _ _ _ _ H).
    - intros r; rewrite existsb_app; cbn [existsb pendWE]; rewrite orb_false_r; exact (r_pend _ _ _ _ _ _ _ H r).
    - intros r; rewrite existsb_app, bitOf_setV, (r_lpend _ _ _ _ _ _ _ H); cbn [existsb pendWL]; rewrite orb_false_r.
      destruct (Zmod.eqb_spec r rd) as [-> | Hne]; [rewrite Zmod.eqb_refl, orb_true_r; reflexivity |].
      rewrite (Zmod_eqb_neq _ rd r (fun He => Hne (eq_sym He))), orb_false_r; reflexivity.
    - rewrite length_filter_app; cbn [filter isPendInt length]; rewrite Nat.add_0_r; exact (r_ib _ _ _ _ _ _ _ H).
    - eapply FUsHold_ext; [| exact (r_fus _ _ _ _ _ _ _ H)]; intros j; rewrite pendIn_app.
      change (pendIn [ELoad rd None] j) with (@nil (type InK)); rewrite app_nil_r; reflexivity.
    - apply NLT_app; split; [exact (r_nlt _ _ _ _ _ _ _ H) | split; [split; [intros r Hr e' [] | exact I] |]].
      intros e0 r He0 Hp e' [<- | []]; split; [| reflexivity].
      cbn [writesR]; apply Zmod_eqb_neq; intros <-; rewrite (Hnp e0 He0) in Hp; discriminate.
    - intros x i d Hin; apply in_app_or in Hin; destruct Hin as [Hin | [Heq | []]];
        [exact (r_route _ _ _ _ _ _ _ H _ _ _ Hin) | discriminate].
  Qed.

  Lemma relC_fill : forall g A p lp ib Ls sigma rd v,
    RelC g A p lp ib Ls sigma -> bitOf lp rd = true ->
    exists pre post, g = pre ++ ELoad rd None :: post /\
      RelC (pre ++ ELoad rd (Some v) :: post) (archSetFpr flen A rd v) p (bitClrV lp rd) ib Ls sigma.
  Proof.
    intros g A p lp ib Ls sigma rd v H Hl.
    rewrite (r_lpend _ _ _ _ _ _ _ H) in Hl; apply existsb_exists in Hl; destruct Hl as [e [He Hpe]].
    destruct e as [| rd' [w |] | | | | |]; cbn [pendWL] in Hpe; try discriminate.
    apply Zmod.eqb_eq in Hpe; subst rd'.
    destruct (in_split _ _ He) as [pre [post Hg]].
    exists pre, post; split; [exact Hg |].
    set (tp := foldSem pre sigma).
    assert (Hn0 := r_nlt _ _ _ _ _ _ _ H); rewrite Hg in Hn0; apply NLT_app in Hn0; destruct Hn0 as [_ [[Hclean _] Hcross]].
    specialize (Hclean rd ltac:(unfold pendW; cbn [pendWE pendWL]; apply Zmod.eqb_refl)).
    assert (Hag : agreeExcept rd (foldSem g sigma) (foldSem (pre ++ ELoad rd (Some v) :: post) sigma)).
    { rewrite Hg, !foldSem_app; unfold foldSem at 1 3; cbn [fold_left entrySem].
      apply agreeExcept_foldSem; split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
      intros r Hr; unfold writeSem; change (archFpr flen tp r = archFpr flen (archSetFpr flen tp rd v) r).
      symmetry; apply archFpr_setFpr_other; exact Hr. }
    assert (Hlast : archFpr flen (foldSem (pre ++ ELoad rd (Some v) :: post) sigma) rd = v).
    { rewrite foldSem_app; unfold foldSem at 1; cbn [fold_left entrySem].
      rewrite archFpr_foldSem_other by (intros e' He'; apply (Hclean e' He')).
      unfold writeSem; apply archFpr_setFpr_same. }
    destruct Hag as [Hfrm [Hff [Hfs Hfpr]]].
    constructor.
    - pose proof (r_cons _ _ _ _ _ _ _ H) as Hc; rewrite Hg in Hc; apply Cons_app in Hc; destruct Hc as [Hc1 [_ Hc2]].
      apply Cons_app; split; [exact Hc1 | split; [exact I |]].
      eapply (Cons_agree rd); [| intros e' He'; apply (Hclean e' He') | exact Hc2].
      split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
      intros r Hr; unfold writeSem; change (archFpr flen (foldSem pre sigma) r = archFpr flen (archSetFpr flen (foldSem pre sigma) rd v) r).
      symmetry; apply archFpr_setFpr_other; exact Hr.
    - intros r Hb; rewrite archFpr_setFpr; destruct (Zmod.eqb_spec r rd) as [-> | Hne]; [symmetry; exact Hlast |].
      rewrite <- (Hfpr r Hne); apply (r_fpr _ _ _ _ _ _ _ H); unfold busyF in *; rewrite bitOf_clrV in Hb.
      rewrite (Zmod_eqb_neq _ _ _ Hne) in Hb; exact Hb.
    - rewrite <- Hfrm; exact (r_frm _ _ _ _ _ _ _ H).
    - rewrite <- Hfs; exact (r_fs _ _ _ _ _ _ _ H).
    - rewrite <- Hff, (r_ff _ _ _ _ _ _ _ H), Hg, !pendFlags_app; reflexivity.
    - intros r; rewrite (r_pend _ _ _ _ _ _ _ H), Hg, !existsb_app3; reflexivity.
    - intros r; rewrite bitOf_clrV, (r_lpend _ _ _ _ _ _ _ H), Hg, !existsb_app3; cbn [pendWL].
      destruct (Zmod.eqb_spec r rd) as [-> | Hne]; [| rewrite (Zmod_eqb_neq _ rd r (fun He => Hne (eq_sym He))); reflexivity].
      rewrite orb_false_r; symmetry; apply orb_false_iff; split; apply existsb_false_intro; intros e' He'.
      + destruct (pendWL e' rd) eqn:Hp; [| reflexivity]; exfalso.
        assert (Hpw : pendW e' rd = true) by (unfold pendW; rewrite Hp, orb_true_r; reflexivity).
        destruct (Hcross e' rd He' Hpw (ELoad rd None) (or_introl eq_refl)) as [Hw _].
        cbn [writesR] in Hw; rewrite Zmod.eqb_refl in Hw; discriminate.
      + destruct (pendWL e' rd) eqn:Hp; [| reflexivity]; exfalso.
        destruct (Hclean e' He') as [Hw _]; rewrite (pendWL_writes _ _ Hp) in Hw; discriminate.
    - rewrite <- (r_ib _ _ _ _ _ _ _ H), Hg, !length_filter_app; reflexivity.
    - eapply FUsHold_ext; [| exact (r_fus _ _ _ _ _ _ _ H)]; intros j; rewrite Hg, !pendIn_app; reflexivity.
    - pose proof (r_nlt _ _ _ _ _ _ _ H) as Hn; rewrite Hg in Hn; apply NLT_app in Hn; destruct Hn as [Hn1 [[_ Hn2] Hn3]].
      apply NLT_app; split; [exact Hn1 | split; [split; [intros r Hr; discriminate | exact Hn2] |]].
      intros e0 r He0 Hp e' [<- | He'];
        [exact (Hn3 e0 r He0 Hp (ELoad rd None) (or_introl eq_refl)) | exact (Hn3 e0 r He0 Hp e' (or_intror He'))].
    - intros x i d Hin; apply (r_route _ _ _ _ _ _ _ H x i d); rewrite Hg.
      apply in_app_or in Hin; apply in_or_app; destruct Hin as [Hin | [Heq | Hin]];
        [left; exact Hin | discriminate | right; right; exact Hin].
  Qed.

  (* ===========================================================================
   * 7. THE STATE AFTER A WRITE-BACK
   * =========================================================================== *)

  Local Abbreviation mkS := (mkIT F xlen narrow ls).

  Lemma wbUpdO_eq : forall A p lp ib Ls (o : type (Option (FUOutK F xlen))) x,
    o @% "data" = fuSpec F xlen wlen narrow x ->
    wbUpdO F xlen narrow lps (mkS A (mkCtl p lp ib) Ls) o = mkS (wbArch A x) (mkCtl (bitClrV p (rdOf x)) lp ib) Ls.
  Proof.
    intros A p lp ib Ls [d [v []]] x Hd; cbn in Hd; subst d.
    unfold wbUpdO, mkIT, wbArch; cbn [Fst Snd]; rewrite evalExpr_Or2; reflexivity.
  Qed.
End RelFpu.
