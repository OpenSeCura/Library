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
 * The pipelined FPU also refines the spec built on the readable reference core
 * (`FpuRefinementRef.v`):
 *
 *   `fpu_refines_ref` : ModSimulationInit (fpuImplMod ... fus) (fpuRefMod ...) RelFpu _
 *
 * `fpuRefMod` (`fpuSpecMod` with `bm = false`) computes every result with `FpCoreRef` (unbiased exponents).  Its
 * results equal the biased ones (`FpCoreRefProof.v`), which is the only hypothesis
 * (`H_bm`) of the generic refinement `fpu_refines`.  The formats must satisfy the side conditions
 * of the equivalence (`FmtOk`; all standard formats do).
 *)

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems.
From Fpu Require Import FpUtil FpCore FpCoreRef SpecFpu FpuFU ImplFpu RelFpu FpuFUProof FpuRefinement FpCoreRefProof.

Import ListNotations.
Local Open Scope Z_scope.

(* Side conditions of the exponent-mode equivalence for one format. *)
Definition FmtOk (G : FpFmt) : Prop :=
  2 <= fmtF G /\ fmtF G + 1 < 2 ^ (fmtE G - 1).

(* All standard formats qualify (and 64-bit `xlen` fits even for binary16). *)
Lemma FmtOk_std : FmtOk FmtS /\ FmtOk FmtD /\ FmtOk FmtH /\ FmtOk FmtQ /\ FmtOk FmtB.
Proof. unfold FmtOk, FmtS, FmtD, FmtH, FmtQ, FmtB; cbn [fmtE fmtF]; repeat split; vm_compute; discriminate. Qed.

Lemma xlen64_ok : forall G, In G [FmtS; FmtD; FmtH; FmtQ; FmtB] -> 64 + 4 <= 7 * 2 ^ (fmtE G - 1).
Proof. intros G HG; repeat (destruct HG as [<- | HG]; [vm_compute; discriminate |]); destruct HG. Qed.

Section RefSpec.
  Variable F : FpFmt.
  Variable xlen : Z.
  Variable narrow : list FpFmt.
  Hypothesis HF : FmtOk F.
  Hypothesis Hx0 : 0 <= xlen.
  Hypothesis Hx1 : xlen + 4 <= 7 * 2 ^ (fmtE F - 1).
  Hypothesis HN : Forall FmtOk narrow.

  Lemma mainRes_ref : forall op rm a b c x,
    evalLetExpr (mainRes false F xlen narrow type op rm a b c x) = evalLetExpr (mainRes true F xlen narrow type op rm a b c x).
  Proof.
    intros; destruct HF as [Hf Hp]; destruct (fmt_cond _ _ Hf Hp) as [He Hfe]; unfold mainRes; cbn [evalLetExpr].
    rewrite (fpuCompute_bm_equiv _ _ _ He Hf Hfe Hx0 Hx1); exact eq_refl.
  Qed.

  Lemma narrowBlock_ref : forall G toN rm a, FmtOk G ->
    evalLetExpr (narrowBlock false F xlen type G toN rm a) = evalLetExpr (narrowBlock true F xlen type G toN rm a).
  Proof.
    intros G toN rm a [Hf2 Hp2]; destruct HF as [Hf Hp].
    destruct (fmt_cond _ _ Hf Hp) as [He Hfe]; destruct (fmt_cond _ _ Hf2 Hp2) as [He2 Hfe2].
    unfold narrowBlock; cbn [evalLetExpr].
    rewrite (cvtFF_bm_equiv _ _ _ _ He2 Hf2 Hfe2 He Hf Hfe), (cvtFF_bm_equiv _ _ _ _ He Hf Hfe He2 Hf2 Hfe2).
    exact eq_refl.
  Qed.

  Lemma narrowSel_ref : forall gs toN rm a nidx k acc, Forall FmtOk gs ->
    evalLetExpr (narrowSel false F xlen narrow type toN rm a nidx gs k acc) =
    evalLetExpr (narrowSel true F xlen narrow type toN rm a nidx gs k acc).
  Proof.
    induction gs as [| G gs IH]; intros toN rm a nidx k acc Hg; [exact eq_refl |].
    inversion Hg as [| ? ? HG Hgs]; subst.
    cbn [narrowSel evalLetExpr]; rewrite (narrowBlock_ref G toN rm a HG); apply IH; exact Hgs.
  Qed.

  Lemma execResOf_ref : forall pkt rm a b c x,
    execResOf false F xlen narrow pkt rm a b c x = execResOf true F xlen narrow pkt rm a b c x.
  Proof.
    intros; unfold execResOf, execCompute; cbn [evalLetExpr].
    rewrite mainRes_ref, (narrowSel_ref narrow) by exact HN; exact eq_refl.
  Qed.

  Variable ms bps : nat.
  Hypothesis H_cfg : PipeCfgOk F ms bps.

  Local Abbreviation lpsStd := (fpuFUsP F xlen narrow ms bps).

  Theorem fpu_refines_ref : forall env1 env2,
    ModSimulationInit env1 env2 (fpuImplMod F xlen narrow (map (fuL F xlen narrow) lpsStd)) (fpuRefMod F xlen narrow)
      (RelFpu F xlen narrow lpsStd) (rel_init F xlen narrow lpsStd (fpuFUsP_ok F xlen narrow ms bps H_cfg)).
  Proof.
    intros env1 env2.
    exact (fpu_refines false F xlen narrow execResOf_ref lpsStd (fpuFUsP_ok F xlen narrow ms bps H_cfg)
             (fpuFUsP_wf F xlen narrow ms bps) env1 env2).
  Qed.
End RefSpec.
