(** * Preservation of fresh function executions.
    The proof composes the concrete pass invariants and stops at the external
    caller boundary.  It does not change the compiler or assume termination. *)

Require Import Coqlib AST Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions Compiler FunctionSpec.
Require Cminortyping RTLtyping Lineartyping ValueAnalysis Separation.

(** Rebind a transition sequence from a global environment to its program.
    Individual transitions are unchanged; only the closure's environment type differs. *)
Lemma program_star:
  forall (P G S: Type) (env: P -> G)
    (step: G -> S -> trace -> S -> Prop) p s t s',
  star step (env p) s t s' ->
  star (fun p => step (env p)) p s t s'.
Proof.
  intros P G S env step p s t s' RUN; induction RUN.
- constructor.
- econstructor; eauto.
Qed.

(** Recover the original global-environment closure after composing program-indexed passes. *)
Lemma program_star_inv:
  forall (P G S: Type) (env: P -> G)
    (step: G -> S -> trace -> S -> Prop) p s t s',
  star (fun p => step (env p)) p s t s' ->
  star step (env p) s t s'.
Proof.
  intros P G S env step p s t s' RUN; induction RUN.
- constructor.
- econstructor; eauto.
Qed.

(** Lift a pass's one-step diagram to finite executions from any matching state. *)
Lemma execution_pass:
  forall (P Q S T: Type)
    (step: P -> S -> trace -> S -> Prop)
    (tstep: Q -> T -> trace -> T -> Prop)
    (programs: P -> Q -> Prop) (states: P -> Q -> S -> T -> Prop),
  (forall p tp, programs p tp ->
   forall s t s', step p s t s' ->
   forall ts, states p tp s ts ->
   exists ts', star tstep tp ts t ts' /\ states p tp s' ts') ->
  execution_preserved step tstep (match_pass programs states).
Proof.
  intros P Q S T step tstep programs states SIM p tp s ts t s'
    [PROG MATCH] RUN.
  cbn in PROG, MATCH. revert ts MATCH. induction RUN; intros ts MATCH.
- exists ts; split; [constructor | split; auto].
- destruct (SIM _ _ PROG _ _ _ H _ MATCH) as (ts2 & RUN2 & MATCH2).
  destruct (IHRUN _ MATCH2) as (ts3 & RUN3 & [_ MATCH3]).
  exists ts3; split; [eapply star_trans; eauto | split; auto].
Qed.

(** Compose execution preservation through an intermediate program and state. *)
Lemma execution_compose:
  forall (P Q U S T V: Type)
    (step: P -> S -> trace -> S -> Prop)
    (mstep: Q -> T -> trace -> T -> Prop)
    (tstep: U -> V -> trace -> V -> Prop)
    (R: P * S -> Q * T -> Prop) (R': Q * T -> U * V -> Prop),
  execution_preserved step mstep R ->
  execution_preserved mstep tstep R' ->
  execution_preserved step tstep (R >>> R').
Proof.
  intros P Q U S T V step mstep tstep R R' FIRST SECOND p tp s ts t s'
    ([mp ms] & MATCH1 & MATCH2) RUN.
  destruct (FIRST _ _ _ _ _ _ MATCH1 RUN) as (ms' & RUN1 & MATCH1').
  destruct (SECOND _ _ _ _ _ _ MATCH2 RUN1) as (ts' & RUN2 & MATCH2').
  exists ts'; split; auto. exists (mp, ms'); auto.
Qed.

(** A skipped optimization is the identity on the program and execution state. *)
Lemma execution_optional:
  forall (P S: Type) (step: P -> S -> trace -> S -> Prop)
    (flag: unit -> bool) (R: P * S -> P * S -> Prop),
  execution_preserved step step R ->
  execution_preserved step step (optional_match flag R).
Proof.
  intros P S step flag R SIM. unfold optional_match.
  destruct (flag tt); auto.
  intros p tp s ts t s' MATCH RUN. inversion MATCH; subst.
  exists s'; split; auto.
Qed.

(** Expand an eventual-match diagram into an ordinary finite-step diagram.
    The stronger stopping predicate prevents advancing past a function return. *)
Lemma eventually_match_step:
  forall (P Q S T: Type)
    (step: P -> S -> trace -> S -> Prop)
    (tstep: Q -> T -> trace -> T -> Prop)
    (final: S -> Integers.int -> Prop) p tp (R: S -> T -> Prop),
  (forall s t s', step p s t s' ->
   forall ts, R s ts ->
   exists ts', star tstep tp ts t ts' /\
     exists n, eventually step final p n s' (fun s'' => R s'' ts')) ->
  forall s t s', step p s t s' ->
  forall ts,
  (exists n, eventually step final p n s (fun s'' => R s'' ts)) ->
  exists ts', star tstep tp ts t ts' /\
    exists n, eventually step final p n s' (fun s'' => R s'' ts').
Proof.
  intros P Q S T step tstep final p tp R SIM s t s' STEP ts [n EV].
  inversion EV as [s0 P0 MATCH | n0 s0 P0 NF NEXT]; subst.
- eapply SIM; eauto.
- destruct (NEXT _ _ STEP) as [EQ EV']; subst t.
  exists ts; split; [constructor | eauto].
Qed.

(** C-to-Clight1 execution preservation uses the existing SimplExprproof diagram. *)
Lemma simpl_expr_execution:
  execution_preserved (fun p => Cstrategy.step (Csem.globalenv p))
    (fun p => Clight.step1 (Clight.globalenv p))
    (match_pass SimplExprproof.match_prog SimplExprproof.match_states).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (SimplExprproof.simulation p tp PROG s t s' STEP ts MATCH) as (ts' & [RUN | [RUN DEC]] & MATCH');
    exists ts'; split; auto; eapply program_star; eauto using plus_star.
Qed.

(** Clight1-to-Clight2 execution preservation uses the existing SimplLocalsproof diagram. *)
Lemma simpl_locals_execution:
  execution_preserved (fun p => Clight.step1 (Clight.globalenv p))
    (fun p => Clight.step2 (Clight.globalenv p))
    (match_pass SimplLocalsproof.match_prog (fun p _ => SimplLocalsproof.match_states p)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (SimplLocalsproof.step_simulation p tp PROG s t s' STEP ts MATCH) as (ts' & RUN & MATCH').
  exists ts'; split; auto; eapply program_star; eauto using plus_star.
Qed.

(** Clight2-to-Csharpminor execution preservation uses the existing Cshmgenproof diagram. *)
Lemma cshmgen_execution:
  execution_preserved (fun p => Clight.step2 (Clight.globalenv p))
    (fun p => Csharpminor.step (Genv.globalenv p))
    (match_pass Cshmgenproof.match_prog Cshmgenproof.match_states).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Cshmgenproof.transl_step p tp PROG s t s' STEP ts MATCH) as (ts' & RUN & MATCH').
  exists ts'; split; auto; eapply program_star; eauto using plus_star.
Qed.

(** Csharpminor-to-Cminor execution preservation uses the existing Cminorgenproof diagram. *)
Lemma cminorgen_execution:
  execution_preserved (fun p => Csharpminor.step (Genv.globalenv p))
    (fun p => Cminor.step (Genv.globalenv p))
    (match_pass Cminorgenproof.match_prog (fun p _ => Cminorgenproof.match_states p)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Cminorgenproof.transl_step_correct p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using plus_star.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** CminorSel-to-RTL execution preservation uses the existing RTLgenproof diagram. *)
Lemma rtlgen_execution:
  execution_preserved (fun p => CminorSel.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass RTLgenproof.match_prog (fun _ _ => RTLgenproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (RTLgenproof.transl_step_correct p tp PROG s t s' STEP ts MATCH) as (ts' & [RUN | [RUN DEC]] & MATCH');
    exists ts'; split; auto; eapply program_star; eauto using plus_star.
Qed.

(** RTL-to-RTL execution preservation uses the existing Tailcallproof diagram. *)
Lemma tailcall_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass Tailcallproof.match_prog (fun _ _ => Tailcallproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Tailcallproof.transf_step_correct p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using star_one.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** RTL-to-RTL execution preservation uses the existing Inliningproof diagram. *)
Lemma inlining_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass Inliningproof.match_prog (fun p _ => Inliningproof.match_states p)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Inliningproof.step_simulation p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using plus_star.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** RTL-to-RTL execution preservation uses the existing Renumberproof diagram. *)
Lemma renumber_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass Renumberproof.match_prog (fun _ _ => Renumberproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Renumberproof.step_simulation p tp PROG s t s' STEP ts MATCH) as (ts' & RUN & MATCH').
  exists ts'; split; auto; eapply program_star; eauto using star_one.
Qed.

(** LTL-to-LTL execution preservation uses the existing Tunnelingproof diagram. *)
Lemma tunneling_execution:
  execution_preserved (fun p => LTL.step (Genv.globalenv p))
    (fun p => LTL.step (Genv.globalenv p))
    (match_pass Tunnelingproof.match_prog (fun _ _ => Tunnelingproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Tunnelingproof.tunnel_step_correct p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using star_one.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** LTL-to-Linear execution preservation uses the existing Linearizeproof diagram. *)
Lemma linearize_execution:
  execution_preserved (fun p => LTL.step (Genv.globalenv p))
    (fun p => Linear.step (Genv.globalenv p))
    (match_pass Linearizeproof.match_prog (fun _ _ => Linearizeproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Linearizeproof.transf_step_correct p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using plus_star.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** Linear-to-Linear execution preservation uses the existing CleanupLabelsproof diagram. *)
Lemma cleanup_execution:
  execution_preserved (fun p => Linear.step (Genv.globalenv p))
    (fun p => Linear.step (Genv.globalenv p))
    (match_pass CleanupLabelsproof.match_prog (fun _ _ => CleanupLabelsproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (CleanupLabelsproof.transf_step_correct p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using star_one.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** Linear-to-Linear execution preservation uses the existing Debugvarproof diagram. *)
Lemma debugvar_execution:
  execution_preserved (fun p => Linear.step (Genv.globalenv p))
    (fun p => Linear.step (Genv.globalenv p))
    (match_pass Debugvarproof.match_prog (fun _ _ => Debugvarproof.match_states)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Debugvarproof.transf_step_correct p tp PROG s t s' STEP ts MATCH) as (ts' & RUN & MATCH').
  exists ts'; split; auto; eapply program_star; eauto using plus_star.
Qed.

(** Mach-to-Asm execution preservation uses the existing Asmgenproof diagram. *)
Lemma asmgen_execution:
  execution_preserved (fun p => Mach.step Asmgenproof0.return_address_offset (Genv.globalenv p))
    (fun p => Asm.step (Genv.globalenv p))
    (match_pass Asmgenproof.match_prog (fun p _ => Asmgenproof.match_states p)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (Asmgenproof.step_simulation p tp PROG s t s' STEP ts MATCH) as [(ts' & RUN & MATCH') | (DEC & EQ & MATCH')].
- exists ts'; split; auto; eapply program_star; eauto using plus_star.
- subst t. exists ts; split; auto using star_refl.
Qed.

(** Instruction selection preserves its typing invariant while accounting for
    source steps that have already been performed by the target. *)
Lemma selection_match_step:
  forall p tp, Selectionproof.match_prog p tp ->
  forall s t s', Cminor.step (Genv.globalenv p) s t s' ->
  forall ts, selection_states p s ts ->
  exists ts', star CminorSel.step (Genv.globalenv tp) ts t ts' /\
              selection_states p s' ts'.
Proof.
  intros p tp PROG s t s' STEP ts MATCH.
  unfold selection_states in *.
  eapply eventually_match_step; [|exact STEP|exact MATCH].
  intros s0 t0 s1 STEP0 ts0 [M W].
  assert (W1: Cminortyping.wt_state s1).
  { eapply Cminortyping.subject_reduction; eauto using Selectionproof.wt_prog. }
  destruct (Selectionproof.sel_step_correct p tp PROG _ _ _ STEP0 _ M W)
    as [(ts1 & RUN & M1) | [(DEC & EQ & M1) | (ts1 & n & RUN & EV)]].
- exists ts1; split; auto using plus_star. exists O; constructor; auto.
- subst t0. exists ts0; split; auto using star_refl. exists O; constructor; auto.
- exists ts1; split; auto using star_one. exists n.
  eapply eventually_and_invariant; eauto.
  intros; eapply Cminortyping.subject_reduction; eauto using Selectionproof.wt_prog.
Qed.

(** Instruction selection preserves finite executions from its concrete state relation. *)
Lemma selection_execution:
  execution_preserved (fun p => Cminor.step (Genv.globalenv p))
    (fun p => CminorSel.step (Genv.globalenv p))
    (match_pass Selectionproof.match_prog (fun p _ => selection_states p)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (selection_match_step _ _ PROG _ _ _ STEP _ MATCH) as (ts' & RUN & M).
  exists ts'; split; auto. eapply program_star; eauto.
Qed.

(** Both value-numbering passes preserve the value-analysis invariant as they
    advance to an eventual match, stopping at the fresh invocation's return. *)
Lemma rtl_analysis_match_step:
  forall p tp (R: RTL.state -> RTL.state -> Prop),
  (forall s t s', RTL.step (Genv.globalenv p) s t s' ->
   forall ts, R s ts -> ValueAnalysis.sound_state p s ->
     (exists ts', RTL.step (Genv.globalenv tp) ts t ts' /\ R s' ts') \/
     (exists ts' n, plus RTL.step (Genv.globalenv tp) ts t ts' /\
       eventually RTL.step RTL.function_final_state (Genv.globalenv p) n s'
         (fun s'' => R s'' ts'))) ->
  forall s t s', RTL.step (Genv.globalenv p) s t s' ->
  forall ts, rtl_eventually p R s ts ->
  exists ts', star RTL.step (Genv.globalenv tp) ts t ts' /\
              rtl_eventually p R s' ts'.
Proof.
  intros p tp R SIM s t s' STEP ts MATCH. unfold rtl_eventually in *.
  eapply eventually_match_step; [|exact STEP|exact MATCH].
  intros s0 t0 s1 STEP0 ts0 [M SOUND].
  assert (SOUND1: ValueAnalysis.sound_state p s1) by
    (eapply ValueAnalysis.sound_step; eauto).
  destruct (SIM _ _ _ STEP0 _ M SOUND) as [(ts1 & RUN & M1) | (ts1 & n & RUN & EV)].
- exists ts1; split; auto using star_one. exists O; constructor; auto.
- exists ts1; split; auto using plus_star. exists n.
  eapply eventually_and_invariant; eauto using ValueAnalysis.sound_step.
Qed.

(** CSE preserves finite executions with sound value-analysis information. *)
Lemma cse_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass CSEproof.match_prog
      (fun p _ => rtl_eventually p (CSEproof.match_states p))).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (rtl_analysis_match_step p tp _ (CSEproof.transf_step_correct p tp PROG)
    _ _ _ STEP _ MATCH) as (ts' & RUN & M).
  exists ts'; split; auto. eapply program_star; eauto.
Qed.

(** Dead-code elimination preserves finite executions with sound value analysis. *)
Lemma deadcode_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass Deadcodeproof.match_prog
      (fun p _ => rtl_eventually p (Deadcodeproof.match_states p))).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts MATCH.
  destruct (rtl_analysis_match_step p tp _ (Deadcodeproof.step_simulation p tp PROG)
    _ _ _ STEP _ MATCH) as (ts' & RUN & M).
  exists ts'; split; auto. eapply program_star; eauto.
Qed.

(** Constant propagation preserves both its simulation index and value-analysis invariant. *)
Lemma constprop_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass Constpropproof.match_prog
      (fun p _ s ts => ValueAnalysis.sound_state p s /\
         exists n, Constpropproof.match_states p n s ts)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts [SOUND [n M]].
  assert (SOUND': ValueAnalysis.sound_state p s') by
    (eapply ValueAnalysis.sound_step; eauto).
  destruct (Constpropproof.transf_step_correct p tp PROG _ _ _ STEP n _ SOUND M)
    as [(n' & ts' & RUN & M') | (n' & DEC & EQ & M')].
- exists ts'; split; [eapply program_star; eauto using star_one | split; eauto].
- subst t. exists ts; split; [constructor | split; eauto].
Qed.

(** Removal of globals preserves executions for the same valid retained set. *)
Lemma unusedglob_execution:
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => RTL.step (Genv.globalenv p))
    (match_pass Unusedglobproof.match_prog
      (fun p tp s ts => exists used,
       Unusedglobproof.valid_used_set p used /\
       Unusedglobproof.match_prog_1 used p tp /\
       Unusedglobproof.match_states p tp used s ts)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts (used & VALID & TRANSF & M).
  destruct (Unusedglobproof.step_simulation p tp used VALID TRANSF _ _ _ STEP _ M)
    as (ts' & RUN & M').
  exists ts'; split; [eapply program_star; eauto using star_one | exists used; auto].
Qed.

(** Register allocation supports the external caller's general result signature
    and preserves the RTL typing invariant throughout the function body. *)
Lemma alloc_execution:
  forall caller,
  execution_preserved (fun p => RTL.step (Genv.globalenv p))
    (fun p => LTL.step (Genv.globalenv p))
    (match_pass Allocproof.match_prog
      (fun _ tp s ts => RTLtyping.wt_state s /\
        Allocproof.match_states tp (Some caller) s ts)).
Proof.
  intros caller. apply execution_pass. intros p tp PROG s t s' STEP ts [WT M].
  destruct (Allocproof.step_simulation p tp PROG (Some caller) _ _ _ STEP WT _ M)
    as (ts' & RUN & M').
  exists ts'; split; [eapply program_star; eauto using plus_star | split; auto].
  eapply RTLtyping.subject_reduction; eauto using Allocproof.wt_prog.
Qed.

(** Stack lowering preserves the external argument area and the Linear typing
    invariant, including accesses to parameters passed in memory. *)
Lemma stacking_execution:
  execution_preserved (fun p => Linear.step (Genv.globalenv p))
    (fun p => Mach.step Asmgenproof0.return_address_offset (Genv.globalenv p))
    (match_pass Stackingproof.match_prog
      (fun p tp s ts => Lineartyping.wt_state s /\
       Stackingproof.match_states Asmgenproof0.return_address_offset p tp s ts)).
Proof.
  apply execution_pass. intros p tp PROG s t s' STEP ts [WT M].
  destruct (Stackingproof.transf_step_correct _ Asmgenproof.return_address_exists
    p tp PROG _ _ _ STEP WT _ M) as (ts' & RUN & M').
  exists ts'; split; [eapply program_star; eauto using plus_star | split; auto].
  eapply Lineartyping.step_type_preservation; eauto using Stackingproof.wt_prog.
Qed.

(** The complete pipeline preserves finite executions between its concrete
    state relations, from Cstrategy through assembly. *)
Theorem function_match_execution:
  forall caller,
  execution_preserved (fun p => Cstrategy.step (Csem.globalenv p))
    (fun p => Asm.step (Genv.globalenv p)) (function_match caller).
Proof.
  intros caller.
  unfold function_match, clight_match, cminor_match, rtl_match.
  repeat eapply execution_compose;
  try apply execution_optional;
  eauto using simpl_expr_execution, simpl_locals_execution, cshmgen_execution,
    cminorgen_execution, selection_execution, rtlgen_execution, tailcall_execution,
    inlining_execution, renumber_execution, constprop_execution, cse_execution,
    deadcode_execution, unusedglob_execution, alloc_execution, tunneling_execution,
    linearize_execution, cleanup_execution, debugvar_execution, stacking_execution,
    asmgen_execution.
Qed.

(** Result and memory correspondence is reflexive before any pass is applied. *)
Lemma value_memory_match_refl:
  forall v m, value_memory_match v m v m.
Proof. intros; left; split; auto using Mem.extends_refl. Qed.

(** Compose value and memory correspondences using CompCert's injection lemmas. *)
Lemma value_memory_match_trans:
  forall v1 m1 v2 m2 v3 m3,
  value_memory_match v1 m1 v2 m2 -> value_memory_match v2 m2 v3 m3 ->
  value_memory_match v1 m1 v3 m3.
Proof.
  intros v1 m1 v2 m2 v3 m3 [ [V1 M1] | [j1 [V1 M1]] ]
    [ [V2 M2] | [j2 [V2 M2]] ].
- left; split; eauto using Val.lessdef_trans, Mem.extends_extends_compose.
- right; exists j2; split;
    eauto using Mem.val_lessdef_inject_compose, Mem.extends_inject_compose.
- right; exists j1; split;
    eauto using Mem.val_inject_lessdef_compose, Mem.inject_extends_compose.
- right; exists (compose_meminj j1 j2); split;
    eauto using val_inject_compose, Mem.inject_compose.
Qed.

(** Compose the return guarantees across consecutive compiler passes. *)
Lemma return_compose:
  forall (P Q U S T V: Type)
    (R: P * S -> Q * T -> Prop) (R': Q * T -> U * V -> Prop)
    ret mret tret,
  return_preserved R ret mret -> return_preserved R' mret tret ->
  return_preserved (R >>> R') ret tret.
Proof.
  intros P Q U S T V R R' ret mret tret FIRST SECOND p tp s ts v m
    ([mp ms] & MATCH1 & MATCH2) RET.
  destruct (FIRST _ _ _ _ _ _ MATCH1 RET) as (mv & mm & MRET & REL1).
  destruct (SECOND _ _ _ _ _ _ MATCH2 MRET) as (tv & tm & TRET & REL2).
  exists tv, tm; split; eauto using value_memory_match_trans.
Qed.

(** A disabled optimization preserves the exact same return state. *)
Lemma return_optional:
  forall (P S: Type) (flag: unit -> bool) (R: P * S -> P * S -> Prop) ret,
  return_preserved R ret ret -> return_preserved (optional_match flag R) ret ret.
Proof.
  intros P S flag R ret PRES. unfold optional_match. destruct (flag tt); auto.
  intros p tp s ts v m EQ RET. inversion EQ; subst.
  exists v, m; auto using value_memory_match_refl.
Qed.

(** An eventual match must hold immediately at any designated function return. *)
Lemma eventually_at_final:
  forall (G S: Type) (step: G -> S -> trace -> S -> Prop) final ge n s P r,
  eventually step final ge n s P -> final s r -> P s.
Proof.
  intros G S step final ge n s P r EV FIN.
  inversion EV as [s0 P0 MATCH | n0 s0 P0 NF NEXT]; subst; auto.
  exfalso; eapply NF; eauto.
Qed.

(** Expression simplification preserves the fresh caller continuation exactly. *)
Lemma simpl_expr_return:
  return_preserved (match_pass SimplExprproof.match_prog SimplExprproof.match_states)
    c_return clight_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold c_return in RET. subst s. inv M.
  specialize (MK p.(Ctypes.prog_comp_env)). inv MK.
  exists v, m; split; [reflexivity | apply value_memory_match_refl].
Qed.

(** Local-variable simplification relates the returned value and memory by injection. *)
Lemma simpl_locals_return:
  return_preserved
    (match_pass SimplLocalsproof.match_prog (fun p _ => SimplLocalsproof.match_states p))
    clight_return clight_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold clight_return in RET. subst s. inv M.
  specialize (MCONT SimplLocals.VSet.empty). inv MCONT.
  eexists; eexists; split; [reflexivity | right; eauto].
Qed.

(** Csharpminor generation preserves the return value, memory, and caller boundary. *)
Lemma cshmgen_return:
  return_preserved (match_pass Cshmgenproof.match_prog Cshmgenproof.match_states)
    clight_return csharpminor_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold clight_return in RET. subst s. inv M. inv MK.
  exists v, m; split; [reflexivity | apply value_memory_match_refl].
Qed.

(** Cminor generation returns to the same boundary through its memory injection. *)
Lemma cminorgen_return:
  return_preserved
    (match_pass Cminorgenproof.match_prog (fun p _ => Cminorgenproof.match_states p))
    csharpminor_return cminor_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold csharpminor_return in RET. subst s. inv M. inv MK.
  eexists; eexists; split; [reflexivity | right; eauto].
Qed.

(** Instruction selection cannot advance its matching relation past a fresh return. *)
Lemma selection_return:
  return_preserved
    (match_pass Selectionproof.match_prog (fun p _ => selection_states p))
    cminor_return cminorsel_return.
Proof.
  intros p tp s ts v m [_ [n EV]] RET. unfold cminor_return in RET. subst s. cbn in EV.
  destruct (eventually_at_final _ _ _ _ _ _ _ _ Integers.Int.zero EV
    (Cminor.function_final_state_intro _ _ _)) as [M WT].
  inv M. inv MC.
  eexists; eexists; split; [reflexivity | left; eauto].
Qed.

(** RTL generation preserves the fresh call's explicit return value and memory. *)
Lemma rtlgen_return:
  return_preserved
    (match_pass RTLgenproof.match_prog (fun _ _ => RTLgenproof.match_states))
    cminorsel_return rtl_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold cminorsel_return in RET. subst s. inv M. inv MS.
  eexists; eexists; split; [reflexivity | left; eauto].
Qed.

(** Tail-call elimination preserves a return to the fresh invocation boundary. *)
Lemma tailcall_return:
  return_preserved
    (match_pass Tailcallproof.match_prog (fun _ _ => Tailcallproof.match_states))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold rtl_return in RET. subst s. inv M.
  match goal with STK: Tailcallproof.match_stackframes nil _ |- _ => inv STK end.
  eexists; eexists; split; [reflexivity | left; eauto].
Qed.

(** Inlining cannot keep execution inside an inlined caller when the source
    has returned all the way to its empty call stack. *)
Lemma inlining_return:
  return_preserved
    (match_pass Inliningproof.match_prog (fun p _ => Inliningproof.match_states p))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold rtl_return in RET. subst s. inv M.
- exploit Inliningproof.match_stacks_empty; eauto. intros EQ; subst.
  eexists; eexists; split; [reflexivity | right; eauto].
- exploit Inliningproof.match_stacks_inside_empty; eauto. intros [EQ BAD]. congruence.
Qed.

(** Renumbering preserves the result and memory exactly at the return boundary. *)
Lemma renumber_return:
  return_preserved
    (match_pass Renumberproof.match_prog (fun _ _ => Renumberproof.match_states))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ M] RET. cbn in M. unfold rtl_return in RET. subst s.
  inv M. inv STACKS. exists v, m; split; [reflexivity | apply value_memory_match_refl].
Qed.

(** Constant propagation preserves the explicit return value up to definedness. *)
Lemma constprop_return:
  return_preserved
    (match_pass Constpropproof.match_prog
      (fun p _ s ts => ValueAnalysis.sound_state p s /\
         exists n, Constpropproof.match_states p n s ts))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ [_ [n M]]] RET. cbn in M.
  unfold rtl_return in RET. subst s. inv M. inv STACKS.
  eexists; eexists; split; [reflexivity | left; eauto].
Qed.

(** CSE preserves the boundary because its eventual match must stop at every return. *)
Lemma cse_return:
  return_preserved
    (match_pass CSEproof.match_prog
      (fun p _ => rtl_eventually p (CSEproof.match_states p)))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ [n EV]] RET.
  unfold rtl_return in RET. subst s. cbn in EV.
  destruct (eventually_at_final _ _ _ _ _ _ _ _ Integers.Int.zero EV
    (RTL.function_final_state_intro _ _ _)) as [M SOUND].
  inv M. inv STACK.
  eexists; eexists; split; [reflexivity | left; eauto].
Qed.

(** Dead-code elimination also stops its eventual matching at the function return. *)
Lemma deadcode_return:
  return_preserved
    (match_pass Deadcodeproof.match_prog
      (fun p _ => rtl_eventually p (Deadcodeproof.match_states p)))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ [n EV]] RET.
  unfold rtl_return in RET. subst s. cbn in EV.
  destruct (eventually_at_final _ _ _ _ _ _ _ _ Integers.Int.zero EV
    (RTL.function_final_state_intro _ _ _)) as [M SOUND].
  inv M. inv STACKS.
  eexists; eexists; split; [reflexivity | left; eauto].
Qed.

(** Global removal preserves the returned value and memory by its block injection. *)
Lemma unusedglob_return:
  return_preserved
    (match_pass Unusedglobproof.match_prog
      (fun p tp s ts => exists used,
       Unusedglobproof.valid_used_set p used /\
       Unusedglobproof.match_prog_1 used p tp /\
       Unusedglobproof.match_states p tp used s ts))
    rtl_return rtl_return.
Proof.
  intros p tp s ts v m [_ [used [_ [_ M]]]] RET. cbn in M.
  unfold rtl_return in RET. subst s. inv M. inv STACKS.
  eexists; eexists; split; [reflexivity | right; eauto].
Qed.

(** Allocation returns the result in the ABI locations for the external caller's
    signature, without restricting the result to an integer type. *)
Lemma alloc_return:
  forall sg saved,
  return_preserved
    (match_pass Allocproof.match_prog
      (fun _ tp s ts => RTLtyping.wt_state s /\
        Allocproof.match_states tp (Some (sg, saved)) s ts))
    rtl_return (ltl_return sg).
Proof.
  intros sg saved p tp s ts v m [_ [_ M]] RET. cbn in M.
  unfold rtl_return in RET. subst s. inv M. inv STACKS; try discriminate.
  match goal with ROOT: Some (sg, saved) = Some _ |- _ => inv ROOT end.
  eexists; eexists; split.
- unfold ltl_return. eexists; eexists; split; reflexivity.
- left; split; auto. erewrite <- loc_result_exten; eauto.
Qed.

(** Reading a register pair preserves the pointwise definedness of location maps. *)
Lemma locmap_result_lessdef:
  forall sg ls tls,
  (forall l, Val.lessdef (ls l) (tls l)) ->
  Val.lessdef (Locmap.getpair (map_rpair R (loc_result sg)) ls)
              (Locmap.getpair (map_rpair R (loc_result sg)) tls).
Proof.
  intros sg ls tls LESS. destruct (loc_result sg); simpl;
    auto using Val.longofwords_lessdef.
Qed.

(** Tunneling preserves the external caller frame and all ABI result locations. *)
Lemma tunneling_return:
  forall sg,
  return_preserved
    (match_pass Tunnelingproof.match_prog (fun _ _ => Tunnelingproof.match_states))
    (ltl_return sg) (ltl_return sg).
Proof.
  intros sg p tp s ts v m [_ M] (saved & ls & EQ & RES). cbn in M; subst s v.
  inv M. inversion STK as [|a al b bl FRAME REST]; subst.
  inv REST. inv FRAME.
  eexists; eexists; split.
- unfold ltl_return. eexists; eexists; split; reflexivity.
- left; split; auto. apply locmap_result_lessdef; auto.
Qed.

(** Linearization preserves the external frame and the result location map. *)
Lemma linearize_return:
  forall sg,
  return_preserved
    (match_pass Linearizeproof.match_prog (fun _ _ => Linearizeproof.match_states))
    (ltl_return sg) (linear_return sg).
Proof.
  intros sg p tp s ts v m [_ M] (saved & ls & EQ & RES). cbn in M; subst s v.
  inv M. match goal with STK: list_forall2 _ (_ :: nil) _ |- _ =>
    inversion STK as [|a al b bl FRAME REST]; subst; inv REST; inv FRAME end.
  eexists; eexists; split.
- unfold linear_return. eexists; eexists; split; reflexivity.
- apply value_memory_match_refl.
Qed.

(** Label cleanup leaves the external caller and returned locations unchanged. *)
Lemma cleanup_return:
  forall sg,
  return_preserved
    (match_pass CleanupLabelsproof.match_prog (fun _ _ => CleanupLabelsproof.match_states))
    (linear_return sg) (linear_return sg).
Proof.
  intros sg p tp s ts v m [_ M] (saved & ls & EQ & RES). cbn in M; subst s v.
  inv M. match goal with STK: list_forall2 _ (_ :: nil) _ |- _ =>
    inversion STK as [|a al b bl FRAME REST]; subst; inv REST; inv FRAME end.
  eexists; eexists; split.
- unfold linear_return. eexists; eexists; split; reflexivity.
- apply value_memory_match_refl.
Qed.

(** Debug information generation preserves the external caller and result locations. *)
Lemma debugvar_return:
  forall sg,
  return_preserved
    (match_pass Debugvarproof.match_prog (fun _ _ => Debugvarproof.match_states))
    (linear_return sg) (linear_return sg).
Proof.
  intros sg p tp s ts v m [_ M] (saved & ls & EQ & RES). cbn in M; subst s v.
  inv M. match goal with STK: list_forall2 _ (_ :: nil) _ |- _ =>
    inversion STK as [|a al b bl FRAME REST]; subst; inv REST; inv FRAME end.
  eexists; eexists; split.
- unfold linear_return. eexists; eexists; split; reflexivity.
- apply value_memory_match_refl.
Qed.

(** Agreement of all machine registers also relates the ABI result register pair. *)
Lemma mach_result_agree:
  forall sg j ls rs,
  Stackingproof.agree_regs j ls rs ->
  Val.inject j (Locmap.getpair (map_rpair R (loc_result sg)) ls) (mach_result sg rs).
Proof.
  intros sg j ls rs AG. unfold mach_result. destruct (loc_result sg); simpl;
    auto using Val.longofwords_inject.
Qed.

(** Stack lowering returns to the external frame and preserves the result and
    memory under the stack-layout injection. *)
Lemma stacking_return:
  forall sg,
  return_preserved
    (match_pass Stackingproof.match_prog
      (fun p tp s ts => Lineartyping.wt_state s /\
       Stackingproof.match_states Asmgenproof0.return_address_offset p tp s ts))
    (linear_return sg) (mach_return sg).
Proof.
  intros sg p tp s ts v m [_ [_ M]] (saved & ls & EQ & RES). cbn in M; subst s v.
  inv M. inv STACKS.
  eexists; eexists; split.
- unfold mach_return. eexists; eexists; split; reflexivity.
- right. eexists; split; [apply mach_result_agree; eauto |].
  apply Separation.sep_proj2 in SEP. apply Separation.sep_proj1 in SEP. exact SEP.
Qed.

(** Assembly register agreement preserves the ABI result selected by the signature. *)
Lemma asm_result_agree:
  forall sg ms sp rs,
  Asmgenproof0.agree ms sp rs ->
  Val.lessdef (mach_result sg ms) (asm_result sg rs).
Proof.
  intros sg ms sp rs AG. unfold mach_result, asm_result, Asm.loc_external_result.
  destruct (loc_result sg); simpl;
    eauto using Asmgenproof0.preg_val, Val.longofwords_lessdef.
Qed.

(** Assembly generation restores the external return address, which is null,
    and preserves the ABI result and final memory. *)
Lemma asmgen_return:
  forall sg,
  return_preserved
    (match_pass Asmgenproof.match_prog (fun p _ => Asmgenproof.match_states p))
    (mach_return sg) (asm_return sg).
Proof.
  intros sg p tp s ts v m [_ M] (sp & ms & EQ & RES). cbn in M; subst s v.
  inv M.
  eexists; eexists; split.
- unfold asm_return. eexists; split; [reflexivity | split; eauto].
- left; split; eauto using asm_result_agree.
Qed.

(** The complete pass relation preserves the function's return boundary,
    ABI result, and final memory for every result signature. *)
Theorem function_match_return:
  forall sg saved,
  return_preserved (function_match (sg, saved)) c_return (asm_return sg).
Proof.
  intros sg saved. unfold function_match, clight_match, cminor_match, rtl_match.
  repeat eapply return_compose;
  try apply return_optional;
  eauto using simpl_expr_return, simpl_locals_return, cshmgen_return,
    cminorgen_return, selection_return, rtlgen_return, tailcall_return,
    inlining_return, renumber_return, constprop_return, cse_return,
    deadcode_return, unusedglob_return, alloc_return, tunneling_return,
    linearize_return, cleanup_return, debugvar_return, stacking_return,
    asmgen_return.
Qed.

