(** * Standalone library correctness, including construction of the entry match. *)

Require Import Coqlib AST Linking Values Memory Globalenvs Events Smallstep.
Require Import Integers Maps Locations Conventions Separation Unusedglob.
Require Import Compiler FunctionSpec Functionproof LibrarySpec.
Require Import ValueDomain ValueAnalysis.

Local Open Scope sep_scope.

(** Valid pointers are unchanged by the flat injection of their own memory. *)
Lemma library_flat_value:
  forall j m tm v tv,
  Mem.inject j m tm -> Val.inject j v tv ->
  Val.inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  intros j m tm v tv MEM VAL; inv VAL; try constructor.
  econstructor. unfold Mem.flat_inj. apply pred_dec_true.
  eapply Mem.valid_block_inject_1; eauto. rewrite Ptrofs.add_zero; reflexivity.
Qed.

(** The same fact applies to the argument list of an ABI call. *)
Lemma library_flat_arguments:
  forall j m tm args targs,
  Mem.inject j m tm -> Val.inject_list j args targs ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args.
Proof.
  intros j m tm args targs MEM VAL; induction VAL; constructor;
    eauto using library_flat_value.
Qed.

(** Extend the initial block classification to caller allocations without
    inventing global symbols or a compiler-owned stack block. *)
Definition library_classification_image (bc: block_classification)
    (old next: block) (b: block) : block_class :=
  if plt b old then bc b else if plt b next then BCother else BCinvalid.

Lemma library_classification_stack:
  forall bc old next,
  bc_nostack bc ->
  forall b1 b2,
  library_classification_image bc old next b1 = BCstack ->
  library_classification_image bc old next b2 = BCstack -> b1 = b2.
Proof.
  intros bc old next NS b1 b2 H.
  unfold library_classification_image in H.
  destruct (plt b1 old); [exfalso; eapply NS; eauto|].
  destruct (plt b1 next); discriminate.
Qed.

Lemma library_classification_global:
  forall bc old next b1 b2 id,
  library_classification_image bc old next b1 = BCglob id ->
  library_classification_image bc old next b2 = BCglob id -> b1 = b2.
Proof.
  intros bc old next b1 b2 id H1 H2.
  unfold library_classification_image in *.
  destruct (plt b1 old); [|destruct (plt b1 next); discriminate].
  destruct (plt b2 old); [|destruct (plt b2 next); discriminate].
  eapply bc_glob; eauto.
Qed.

(** The classification contains exactly the initial global names and all valid
    caller blocks; its construction is used only inside the proof. *)
Definition library_classification (bc: block_classification) (old next: block)
    (NS: bc_nostack bc) : block_classification :=
  BC (library_classification_image bc old next)
    (library_classification_stack bc old next NS)
    (library_classification_global bc old next).

(** Constant-memory facts transfer across caller allocations and mutations of
    writable data.  Only blocks known to be read-only are inspected. *)
Lemma library_romatch:
  forall bc oldm m rm,
  bc_below bc (Mem.nextblock oldm) ->
  library_constants oldm m ->
  romatch bc oldm rm -> romatch bc m rm.
Proof.
  intros bc oldm m rm BELOW CONST RO.
  intros b id ab NAME LOOKUP.
  destruct (RO _ _ _ NAME LOOKUP) as (SUMMARY & CONTENTS & NOWRITE).
  destruct (CONST b) as [LOADS PERMS].
  { apply BELOW; congruence. }
  { exact NOWRITE. }
  split; auto. split.
- eapply bmatch_ext; eauto.
- intros ofs WRITE. eapply NOWRITE. eapply PERMS; eauto.
Qed.

(** A well-formed source heap with unchanged constants satisfies value analysis
    at any fresh function call, even after mutable globals and caller data change. *)
Lemma library_sound_call:
  forall p initial m fd args,
  Genv.init_mem p = Some initial ->
  Ple (Mem.nextblock initial) (Mem.nextblock m) ->
  library_constants initial m ->
  Mem.inject_neutral (Mem.nextblock m) m ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args ->
  sound_state p (RTL.Callstate nil fd args m).
Proof.
  intros p initial m fd args INIT LE CONST NEUTRAL ARGS.
  destruct (initial_mem_matches p initial INIT)
    as (bc & GE & BELOW & NS & RO & VALID).
  pose (bc' := library_classification bc (Mem.nextblock initial) (Mem.nextblock m) NS).
  assert (GLOB: forall b id, bc' b = BCglob id <-> bc b = BCglob id).
  { intros b id. unfold bc', library_classification; simpl.
    unfold library_classification_image.
    destruct (plt b (Mem.nextblock initial)); [tauto|].
    destruct (plt b (Mem.nextblock m)); split; intro H; try discriminate;
      exfalso; apply n; apply BELOW; congruence. }
  assert (OTHER: forall b, bc b = BCother -> bc' b = BCother).
  { intros b H. unfold bc', library_classification; simpl.
    unfold library_classification_image. rewrite pred_dec_true by (apply BELOW; congruence).
    exact H. }
  assert (GE': genv_match bc' (Genv.globalenv p)).
  { eapply genv_match_exten; eauto. intros; symmetry; apply GLOB. }
  assert (NS': bc_nostack bc').
  { intros b. unfold bc', library_classification; simpl.
    unfold library_classification_image. destruct (plt b (Mem.nextblock initial)); auto.
    destruct (plt b (Mem.nextblock m)); congruence. }
  assert (INJ: inj_of_bc bc' = Mem.flat_inj (Mem.nextblock m)).
  { apply Axioms.extensionality; intros b.
    unfold inj_of_bc, bc', library_classification; simpl.
    unfold library_classification_image, Mem.flat_inj.
    destruct (plt b (Mem.nextblock initial)) as [OLD|OLD].
    - rewrite pred_dec_true by (eapply Plt_Ple_trans; eauto).
      destruct (bc b) eqn:BC; auto. exfalso; exact (VALID b OLD BC).
    - destruct (plt b (Mem.nextblock m)); reflexivity. }
  assert (ARGMATCH: forall al tl,
      Val.inject_list (Mem.flat_inj (Mem.nextblock m)) al tl ->
      forall v, In v al -> vmatch bc' v Vtop).
  { intros al tl REL. induction REL; simpl; intros x IN.
    - contradiction.
    - destruct IN as [EQ|IN].
      + subst x. eapply vmatch_inj_top. rewrite INJ. eauto.
      + eauto. }
  constructor; intros cunit LINK. eapply sound_call_state with bc'.
- constructor.
- eapply ARGMATCH; eauto.
- eapply romatch_exten.
  + eapply library_romatch; eauto.
  + intros; apply GLOB.
- eapply mmatch_inj_top. rewrite INJ. apply Mem.neutral_inject; auto.
- exact GE'.
- exact NS'.
Qed.

(** Passes that do not remove globals keep symbol addresses, global bounds,
    initialized data, and the list of public names unchanged. *)
Definition library_layout {F V TF TV: Type}
    (p: AST.program F V) (tp: AST.program TF TV) : Prop :=
  (forall id, Genv.find_symbol (Genv.globalenv tp) id =
              Genv.find_symbol (Genv.globalenv p) id) /\
  Genv.genv_next (Genv.globalenv tp) = Genv.genv_next (Genv.globalenv p) /\
  (forall m, Genv.init_mem p = Some m -> Genv.init_mem tp = Some m) /\
  tp.(prog_public) = p.(prog_public).

Lemma library_layout_refl:
  forall F V (p: AST.program F V), library_layout p p.
Proof. intros; repeat split; auto. Qed.

Lemma library_layout_trans:
  forall F V MF MV TF TV (p: AST.program F V)
    (mp: AST.program MF MV) (tp: AST.program TF TV),
  library_layout p mp -> library_layout mp tp -> library_layout p tp.
Proof.
  intros F V MF MV TF TV p mp tp (S1 & N1 & I1 & P1) (S2 & N2 & I2 & P2).
  repeat split; intros; eauto; congruence.
Qed.

Section PROGRAM_LAYOUT.
Context {C F V TF TV: Type} {LC: Linker C} {LF: Linker F} {LV: Linker V}.
Lemma library_match_layout:
  forall (RF: C -> F -> TF -> Prop) (RV: V -> TV -> Prop) ctx p tp,
  match_program_gen RF RV ctx p tp -> library_layout p tp.
Proof.
  intros RF RV ctx p tp MATCH. repeat split.
- exact (Genv.find_symbol_match MATCH).
- exact (Genv.mge_next (Genv.globalenvs_match MATCH)).
- exact (Genv.init_mem_match MATCH).
- exact (match_program_public RF RV ctx p tp MATCH).
Qed.
End PROGRAM_LAYOUT.

(** Flat self-injections preserve source global references at fresh calls. *)
Lemma library_simpllocals_globals:
  forall p m,
  Ple (Genv.genv_next (Genv.globalenv (Ctypes.program_of_program p))) (Mem.nextblock m) ->
  SimplLocalsproof.match_globalenvs p (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
Proof.
  intros p m LE. constructor; intros.
- unfold Mem.flat_inj; apply pred_dec_true; auto.
- unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m)); congruence.
- eapply Plt_Ple_trans; [eapply Genv.genv_symb_range; eauto|exact LE].
- apply Genv.find_funct_ptr_iff in H.
  eapply Plt_Ple_trans; [eapply Genv.genv_defs_range; eauto|exact LE].
- apply Genv.find_var_info_iff in H.
  eapply Plt_Ple_trans; [eapply Genv.genv_defs_range; eauto|exact LE].
Qed.

Lemma library_cminorgen_globals:
  forall p m,
  Ple (Genv.genv_next (Genv.globalenv p)) (Mem.nextblock m) ->
  Cminorgenproof.match_globalenvs p (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
Proof.
  intros p m LE. constructor; intros.
- unfold Mem.flat_inj; apply pred_dec_true; auto.
- unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m)); congruence.
- eapply Plt_Ple_trans; [eapply Genv.genv_symb_range; eauto|exact LE].
- apply Genv.find_funct_ptr_iff in H.
  eapply Plt_Ple_trans; [eapply Genv.genv_defs_range; eauto|exact LE].
- apply Genv.find_var_info_iff in H.
  eapply Plt_Ple_trans; [eapply Genv.genv_defs_range; eauto|exact LE].
Qed.

Lemma library_inlining_globals:
  forall p m,
  Ple (Genv.genv_next (Genv.globalenv p)) (Mem.nextblock m) ->
  Inliningproof.match_globalenvs p (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
Proof.
  intros p m LE. constructor; intros.
- unfold Mem.flat_inj; apply pred_dec_true; auto.
- unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m)); congruence.
- eapply Plt_Ple_trans; [eapply Genv.genv_symb_range; eauto|exact LE].
- apply Genv.find_funct_ptr_iff in H.
  eapply Plt_Ple_trans; [eapply Genv.genv_defs_range; eauto|exact LE].
- apply Genv.find_var_info_iff in H.
  eapply Plt_Ple_trans; [eapply Genv.genv_defs_range; eauto|exact LE].
Qed.

(** Expression simplification establishes its own fresh-call state relation. *)
Lemma library_simpl_expr_entry:
  forall p tp b fd args m,
  SimplExprproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv (Ctypes.program_of_program p)) b = Some fd ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv (Ctypes.program_of_program tp)) b = Some tfd /\
    Clight.type_of_fundef tfd = Csyntax.type_of_fundef fd /\
    SimplExprproof.match_states p tp
      (Csem.Callstate fd args Csem.Kstop m) (Clight.Callstate tfd args Clight.Kstop m).
Proof.
  intros p tp b fd args m PROG FIND.
  destruct (SimplExprproof.function_ptr_translated p tp PROG b fd FIND)
    as (cu & tfd & TFIND & TRANS & LINK).
  exists tfd; split; auto. split.
- eapply SimplExprproof.type_of_fundef_preserved; eauto.
- econstructor; eauto. intros; constructor.
Qed.

(** Local simplification derives its boundary from the source heap's ordinary
    self-injection and the normalized C arguments. *)
Lemma library_simpl_locals_entry:
  forall p tp b fd args m targs tres cc,
  SimplLocalsproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv (Ctypes.program_of_program p)) b = Some fd ->
  Clight.type_of_fundef fd = Ctypes.Tfunction targs tres cc ->
  SimplLocalsproof.val_casted_list args targs ->
  Ple (Genv.genv_next (Genv.globalenv (Ctypes.program_of_program p))) (Mem.nextblock m) ->
  Mem.inject_neutral (Mem.nextblock m) m ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv (Ctypes.program_of_program tp)) b = Some tfd /\
    Clight.type_of_fundef tfd = Clight.type_of_fundef fd /\
    SimplLocalsproof.match_states p
      (Clight.Callstate fd args Clight.Kstop m) (Clight.Callstate tfd args Clight.Kstop m).
Proof.
  intros p tp b fd args m targs tres cc PROG FIND TY CAST LE NEUTRAL ARGS.
  destruct (SimplLocalsproof.function_ptr_translated p tp PROG b fd FIND)
    as (tfd & TFIND & TRANS).
  exists tfd; split; auto. split.
- eapply SimplLocalsproof.type_of_fundef_preserved; eauto.
- econstructor; eauto using Mem.neutral_inject.
  intros cenv. econstructor; eauto using library_simpllocals_globals, Ple_refl.
Qed.

(** Already normalized C arguments have the strict machine argument types. *)
Lemma library_cast_arguments:
  forall args tys,
  SimplLocalsproof.val_casted_list args tys ->
  Val.has_argtype_list args (List.map Ctypes.argtype_of_type tys).
Proof.
  intros args tys CAST; induction CAST; constructor; auto using Cop.val_casted_has_argtype.
Qed.

Lemma library_cshmgen_entry:
  forall p tp b fd args m targs tres cc,
  Cshmgenproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv (Ctypes.program_of_program p)) b = Some fd ->
  Clight.type_of_fundef fd = Ctypes.Tfunction targs tres cc ->
  Val.has_argtype_list args (List.map Ctypes.argtype_of_type targs) ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    Csharpminor.funsig tfd = Ctypes.signature_of_type targs tres cc /\
    Cshmgenproof.match_states p tp
      (Clight.Callstate fd args Clight.Kstop m)
      (Csharpminor.Callstate tfd args Csharpminor.Kstop m).
Proof.
  intros p tp b fd args m targs tres cc PROG FIND TY ARGS.
  destruct (Cshmgenproof.function_ptr_translated p tp PROG b fd FIND)
    as (cu & tfd & TFIND & TRANS & LINK).
  exists tfd; split; auto. split.
- eapply Cshmgenproof.transl_fundef_sig2; eauto.
- eapply Cshmgenproof.match_callstate with (cu := cu)
    (ce := Ctypes.prog_comp_env cu); eauto. constructor. exact Logic.I.
Qed.

Lemma library_cminorgen_entry:
  forall p tp b fd args m,
  Cminorgenproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  Ple (Genv.genv_next (Genv.globalenv p)) (Mem.nextblock m) ->
  Mem.inject_neutral (Mem.nextblock m) m ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    Cminor.funsig tfd = Csharpminor.funsig fd /\
    Cminorgenproof.match_states p
      (Csharpminor.Callstate fd args Csharpminor.Kstop m)
      (Cminor.Callstate tfd args Cminor.Kstop m).
Proof.
  intros p tp b fd args m PROG FIND LE NEUTRAL ARGS.
  destruct (Cminorgenproof.function_ptr_translated p tp PROG b fd FIND)
    as (tfd & TFIND & TRANS).
  exists tfd; split; auto. split.
- eapply Cminorgenproof.sig_preserved; eauto.
- eapply Cminorgenproof.match_callstate with
    (f := Mem.flat_inj (Mem.nextblock m)) (cs := nil) (cenv := PTree.empty Z);
    eauto using Mem.neutral_inject.
  + econstructor; eauto using library_cminorgen_globals, Ple_refl.
  + constructor.
  + exact Logic.I.
Qed.

Lemma library_lessdef_arguments: forall args, Val.lessdef_list args args.
Proof. induction args; constructor; auto. Qed.

Lemma library_selection_entry:
  forall p tp b fd args m,
  Selectionproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  Val.has_type_list args (proj_sig_args (Cminor.funsig fd)) ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    CminorSel.funsig tfd = Cminor.funsig fd /\
    selection_states p (Cminor.Callstate fd args Cminor.Kstop m)
      (CminorSel.Callstate tfd args CminorSel.Kstop m).
Proof.
  intros p tp b fd args m PROG FIND ARGS.
  destruct (Selectionproof.function_ptr_translated p tp PROG b fd FIND)
    as (cu & tfd & TFIND & TRANS & LINK).
  exists tfd; split; auto. split.
- eapply Selectionproof.sig_function_translated; eauto.
- exists O; constructor; split.
  + econstructor; eauto using library_lessdef_arguments, Mem.extends_refl. constructor.
  + econstructor; eauto.
    * eapply Genv.find_funct_ptr_prop; [exact (Selectionproof.wt_prog p tp PROG) | exact FIND].
    * constructor.
Qed.

Lemma library_rtlgen_entry:
  forall p tp b fd args m,
  RTLgenproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = CminorSel.funsig fd /\
    RTLgenproof.match_states (CminorSel.Callstate fd args CminorSel.Kstop m)
      (RTL.Callstate nil tfd args m).
Proof.
  intros p tp b fd args m PROG FIND.
  destruct (RTLgenproof.function_ptr_translated p tp PROG b fd FIND)
    as (tfd & TFIND & TRANS).
  exists tfd; split; auto. split.
- eapply RTLgenproof.sig_transl_function; eauto.
- econstructor; eauto using library_lessdef_arguments, Mem.extends_refl. constructor.
Qed.

Lemma library_tailcall_entry:
  forall p tp b fd args m,
  Tailcallproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    Tailcallproof.match_states (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m).
Proof.
  intros p tp b fd args m PROG FIND.
  exists (Tailcall.transf_fundef fd); split.
- eapply Tailcallproof.funct_ptr_translated; eauto.
- split; [apply Tailcallproof.sig_preserved |].
  econstructor; eauto using library_lessdef_arguments, Mem.extends_refl. constructor.
Qed.

Lemma library_inlining_entry:
  forall p tp b fd args m,
  Inliningproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  Ple (Genv.genv_next (Genv.globalenv p)) (Mem.nextblock m) ->
  Mem.inject_neutral (Mem.nextblock m) m ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    Inliningproof.match_states p (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m).
Proof.
  intros p tp b fd args m PROG FIND LE NEUTRAL ARGS.
  destruct (Inliningproof.function_ptr_translated p tp PROG b fd FIND)
    as (cu & tfd & TFIND & TRANS & LINK).
  exists tfd; split; auto. split.
- eapply Inliningproof.sig_function_translated; eauto.
- eapply Inliningproof.match_call_states with (F := Mem.flat_inj (Mem.nextblock m));
    eauto using Mem.neutral_inject.
  econstructor; eauto using library_inlining_globals, Ple_refl.
Qed.

Lemma library_renumber_entry:
  forall p tp b fd args m,
  Renumberproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    Renumberproof.match_states (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m).
Proof.
  intros p tp b fd args m PROG FIND.
  exists (Renumber.transf_fundef fd); split.
- eapply Renumberproof.function_ptr_translated; eauto.
- split; [apply Renumberproof.sig_preserved |]. constructor; constructor.
Qed.

Lemma library_constprop_entry:
  forall p tp b fd args m,
  Constpropproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  ValueAnalysis.sound_state p (RTL.Callstate nil fd args m) ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    (ValueAnalysis.sound_state p (RTL.Callstate nil fd args m) /\
     exists n, Constpropproof.match_states p n
       (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m)).
Proof.
  intros p tp b fd args m PROG FIND SOUND.
  destruct (Constpropproof.function_ptr_translated p tp PROG b fd FIND) as (cu & TFIND & LINK).
  eexists; split; [exact TFIND |]. split; [apply Constpropproof.sig_function_translated |].
  split; auto. exists O. econstructor; eauto using library_lessdef_arguments, Mem.extends_refl.
  constructor.
Qed.

Lemma library_cse_entry:
  forall p tp b fd args m,
  CSEproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  ValueAnalysis.sound_state p (RTL.Callstate nil fd args m) ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    rtl_eventually p (CSEproof.match_states p)
      (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m).
Proof.
  intros p tp b fd args m PROG FIND SOUND.
  destruct (CSEproof.funct_ptr_translated p tp PROG b fd FIND)
    as (cu & tfd & TFIND & TRANS & LINK).
  exists tfd; split; auto. split.
- eapply CSEproof.sig_preserved; eauto.
- exists O; constructor; split; auto.
  econstructor; eauto using library_lessdef_arguments, Mem.extends_refl. constructor.
Qed.

Lemma library_deadcode_entry:
  forall p tp b fd args m,
  Deadcodeproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  ValueAnalysis.sound_state p (RTL.Callstate nil fd args m) ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    rtl_eventually p (Deadcodeproof.match_states p)
      (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m).
Proof.
  intros p tp b fd args m PROG FIND SOUND.
  destruct (Deadcodeproof.function_ptr_translated p tp PROG b fd FIND)
    as (cu & tfd & TFIND & TRANS & LINK).
  exists tfd; split; auto. split.
- eapply Deadcodeproof.sig_function_translated; eauto.
- exists O; constructor; split; auto.
  econstructor; eauto using library_lessdef_arguments, Mem.extends_refl. constructor.
Qed.

(** Optional passes keep the same call when disabled. *)
Lemma library_optional_rtl_entry:
  forall flag (P: RTL.program -> RTL.program -> Prop)
    (R: RTL.program -> RTL.program -> RTL.state -> RTL.state -> Prop) p tp b fd args m,
  match_if flag P p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  (P p tp -> forall b fd,
     Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
     exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
       RTL.funsig tfd = RTL.funsig fd /\
       R p tp (RTL.Callstate nil fd args m) (RTL.Callstate nil tfd args m)) ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    RTL.funsig tfd = RTL.funsig fd /\
    optional_match flag (match_pass P R)
      (p, RTL.Callstate nil fd args m) (tp, RTL.Callstate nil tfd args m).
Proof.
  intros flag P R p tp b fd args m PROG FIND ENTRY.
  unfold match_if in PROG; unfold optional_match.
  destruct (flag tt).
- destruct (ENTRY PROG b fd FIND) as (tfd & TFIND & SIG & REL).
  exists tfd; repeat split; auto.
- subst tp. exists fd; auto.
Qed.

Lemma library_optional_layout:
  forall A (flag: unit -> bool) (P: A -> A -> Prop) (L: A -> A -> Prop),
  (forall p, L p p) -> (forall p tp, P p tp -> L p tp) ->
  forall p tp, match_if flag P p tp -> L p tp.
Proof. intros A flag P L REFL PASS p tp H; unfold match_if in H.
  destruct (flag tt); eauto. subst; auto.
Qed.

Lemma library_symbols_transport:
  forall F V TF TV F' V' TF' TV'
    (ge: Genv.t F V) (tge: Genv.t TF TV)
    (ge': Genv.t F' V') (tge': Genv.t TF' TV') j,
  (forall id, Genv.find_symbol ge' id = Genv.find_symbol ge id) ->
  (forall id, Genv.find_symbol tge' id = Genv.find_symbol tge id) ->
  Genv.genv_next ge' = Genv.genv_next ge ->
  Genv.genv_next tge' = Genv.genv_next tge ->
  library_symbols ge tge j -> library_symbols ge' tge' j.
Proof.
  intros F V TF TV F' V' TF' TV' ge tge ge' tge' j S TS N TN H.
  destruct H as [A B C]; constructor.
- intros b tb delta INJ LT. rewrite N in LT.
  destruct (A b tb delta INJ LT) as (id & X & Y & Z).
  exists id; rewrite S, TS; auto.
- intros b tb delta INJ LT. rewrite TN in LT.
  destruct (B b tb delta INJ LT) as (id & X & Y & Z).
  exists id; rewrite S, TS; auto.
- intros id b tb X Y. rewrite S in X; rewrite TS in Y; eauto.
Qed.

Lemma library_pruning_globals:
  forall p tp used j,
  Unusedglobproof.valid_used_set p used ->
  Unusedglobproof.match_prog_1 used p tp ->
  library_symbols (Genv.globalenv p) (Genv.globalenv tp) j ->
  Unusedglobproof.meminj_preserves_globals p tp used j.
Proof.
  intros p tp used j VALID PROG [SOURCE TARGET COMMON].
  assert (NAME: forall id id' b,
    Genv.find_symbol (Genv.globalenv p) id = Some b ->
    Genv.find_symbol (Genv.globalenv p) id' = Some b -> id = id').
  { intros. apply Genv.find_invert_symbol in H. apply Genv.find_invert_symbol in H0. congruence. }
  constructor.
- intros id b tb delta INJ SYM.
  destruct (SOURCE b tb delta INJ (Genv.genv_symb_range _ _ SYM))
    as (id' & SYM' & TSYM & ZERO).
  assert (id = id') by (eapply NAME; eauto). subst; auto.
- intros id b KEEP SYM.
  destruct (Unusedglobproof.transform_find_symbol_1 p tp used PROG id b SYM KEEP)
    as (tb & TSYM).
  exists tb; split; auto. eapply COMMON; eauto.
- intros id tb TSYM.
  destruct (Unusedglobproof.transform_find_symbol_2 p tp used PROG id tb TSYM)
    as (KEEP & b & SYM).
  exists b; split; auto. eapply COMMON; eauto.
- intros b tb delta gd INJ DEF.
  destruct (SOURCE b tb delta INJ (Genv.genv_defs_range _ _ DEF))
    as (id & SYM & TSYM & ZERO).
  assert (DM: (prog_defmap p)!id = Some gd).
  { apply Genv.find_def_symbol. exists b; auto. }
  destruct (Unusedglobproof.transform_find_symbol_2 p tp used PROG id tb TSYM)
    as (KEEP & X).
  assert (TDM: (prog_defmap tp)!id = Some gd).
  { rewrite (Unusedglobproof.match_prog_def _ _ _ PROG), IS.mem_1 by exact KEEP. exact DM. }
  apply Genv.find_def_symbol in TDM. destruct TDM as (tb' & TSYM' & TDEF).
  assert (tb' = tb) by congruence. subst tb'.
  split; auto. split; auto. intros id' REF.
  eapply Unusedglobproof.used_closed; eauto.
- intros b tb delta gd INJ TDEF.
  destruct (TARGET b tb delta INJ (Genv.genv_defs_range _ _ TDEF))
    as (id & SYM & TSYM & ZERO).
  assert (TDM: (prog_defmap tp)!id = Some gd).
  { apply Genv.find_def_symbol. exists tb; auto. }
  rewrite (Unusedglobproof.match_prog_def _ _ _ PROG) in TDM.
  destruct (IS.mem id used) eqn:KEEP; try discriminate.
  apply Genv.find_def_symbol in TDM. destruct TDM as (b' & SYM' & DEF).
  assert (b' = b) by congruence. subst b'; auto.
Qed.

Lemma library_unusedglob_entry:
  forall p tp used j id b tb fd args targs m tm,
  Unusedglobproof.valid_used_set p used ->
  Unusedglobproof.match_prog_1 used p tp ->
  library_symbols (Genv.globalenv p) (Genv.globalenv tp) j ->
  In id (prog_public p) ->
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  Genv.find_symbol (Genv.globalenv tp) id = Some tb ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  Ple (Genv.genv_next (Genv.globalenv p)) (Mem.nextblock m) ->
  Ple (Genv.genv_next (Genv.globalenv tp)) (Mem.nextblock tm) ->
  Mem.inject j m tm -> Val.inject_list j args targs ->
  Genv.find_funct_ptr (Genv.globalenv tp) tb = Some fd /\
  Unusedglobproof.match_states p tp used
    (RTL.Callstate nil fd args m) (RTL.Callstate nil fd targs tm).
Proof.
  intros p tp used j id b tb fd args targs m tm VALID PROG SYMBOLS PUBLIC SYM TSYM FIND LE TLE MEM ARGS.
  pose proof (library_pruning_globals p tp used j VALID PROG SYMBOLS) as GLOBALS.
  pose proof (library_common_symbol _ _ _ SYMBOLS id b tb SYM TSYM) as INJ.
  apply Genv.find_funct_ptr_iff in FIND.
  destruct (Unusedglobproof.defs_inject _ _ _ _ GLOBALS b tb 0 _ INJ FIND)
    as (TFIND & ZERO & KEEP).
  split; [apply Genv.find_funct_ptr_iff; auto |].
  eapply Unusedglobproof.match_states_call; eauto.
  constructor; auto.
Qed.

Lemma library_allocation_entry:
  forall p tp b fd saved sg m,
  Allocproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd ->
  RTL.funsig fd = sg ->
  Val.has_type_list (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments sg))
    (proj_sig_args sg) ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    LTL.funsig tfd = sg /\
    (RTLtyping.wt_state (RTL.Callstate nil fd
      (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments sg)) m) /\
    Allocproof.match_states tp (Some (sg, saved))
      (RTL.Callstate nil fd (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments sg)) m)
      (LTL.Callstate (LTL.ExternalFrame sg saved :: nil) tfd saved m)).
Proof.
  intros p tp b fd saved sg m PROG FIND SIG ARGS.
  destruct (Allocproof.function_ptr_translated p tp PROG b fd FIND) as (tfd & TFIND & TRANS).
  assert (TSIG: LTL.funsig tfd = sg) by (erewrite Allocproof.sig_function_translated; eauto).
  exists tfd; split; auto. split; auto. split.
- apply RTLtyping.wt_state_call.
  + constructor.
  + eapply Genv.find_funct_ptr_prop; [exact (Allocproof.wt_prog p tp PROG) | exact FIND].
  + rewrite SIG; exact ARGS.
- econstructor; rewrite ?TSIG; eauto using Mem.extends_refl, library_lessdef_arguments.
  + constructor; auto.
  + red; simpl; auto.
Qed.

Lemma library_tunneling_entry:
  forall p tp b fd saved sg m,
  Tunnelingproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd -> LTL.funsig fd = sg ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    LTL.funsig tfd = sg /\
    Tunnelingproof.match_states
      (LTL.Callstate (LTL.ExternalFrame sg saved :: nil) fd saved m)
      (LTL.Callstate (LTL.ExternalFrame sg saved :: nil) tfd saved m).
Proof.
  intros p tp b fd saved sg m PROG FIND SIG.
  exists (Tunneling.tunnel_fundef fd); split.
- eapply Tunnelingproof.function_ptr_translated; eauto.
- split; [rewrite Tunnelingproof.sig_preserved; auto |].
  econstructor; eauto using Mem.extends_refl.
  + constructor; [constructor; red; auto | constructor].
  + red; auto.
Qed.

Lemma library_linearize_entry:
  forall p tp b fd saved sg m,
  Linearizeproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd -> LTL.funsig fd = sg ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    Linear.funsig tfd = sg /\
    Linearizeproof.match_states
      (LTL.Callstate (LTL.ExternalFrame sg saved :: nil) fd saved m)
      (Linear.Callstate (Linear.ExternalFrame sg saved :: nil) tfd saved m).
Proof.
  intros p tp b fd saved sg m PROG FIND SIG.
  destruct (Linearizeproof.function_ptr_translated p tp PROG b fd FIND) as (tfd & TFIND & TRANS).
  exists tfd; split; auto. split.
- erewrite Linearizeproof.sig_preserved; eauto.
- econstructor; eauto. constructor; constructor.
Qed.

Lemma library_cleanup_entry:
  forall p tp b fd saved sg m,
  CleanupLabelsproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd -> Linear.funsig fd = sg ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    Linear.funsig tfd = sg /\
    CleanupLabelsproof.match_states
      (Linear.Callstate (Linear.ExternalFrame sg saved :: nil) fd saved m)
      (Linear.Callstate (Linear.ExternalFrame sg saved :: nil) tfd saved m).
Proof.
  intros p tp b fd saved sg m PROG FIND SIG.
  exists (CleanupLabels.transf_fundef fd); split.
- eapply CleanupLabelsproof.function_ptr_translated; eauto.
- split; [rewrite CleanupLabelsproof.sig_function_translated; auto |].
  constructor; constructor; constructor.
Qed.

Lemma library_debug_entry:
  forall p tp b fd saved sg m,
  match_if Compopts.debug Debugvarproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd -> Linear.funsig fd = sg ->
  exists tfd, Genv.find_funct_ptr (Genv.globalenv tp) b = Some tfd /\
    Linear.funsig tfd = sg /\
    optional_match Compopts.debug
      (match_pass Debugvarproof.match_prog (fun _ _ => Debugvarproof.match_states))
      (p, Linear.Callstate (Linear.ExternalFrame sg saved :: nil) fd saved m)
      (tp, Linear.Callstate (Linear.ExternalFrame sg saved :: nil) tfd saved m).
Proof.
  intros p tp b fd saved sg m PROG FIND SIG.
  unfold match_if in PROG; unfold optional_match. destruct (Compopts.debug tt).
- destruct (Debugvarproof.function_ptr_translated p tp PROG b fd FIND) as (tfd & TFIND & TRANS).
  exists tfd; split; auto. split.
  + erewrite Debugvarproof.sig_preserved; eauto.
  + split; auto. econstructor; eauto. constructor; constructor.
- subst tp; exists fd; auto.
Qed.

Lemma library_globalenv_assertion:
  forall F V (ge: Genv.t F V) k m,
  library_global_identity k (Genv.genv_next ge) ->
  Ple (Genv.genv_next ge) (Mem.nextblock m) ->
  m |= globalenv_inject ge k.
Proof.
  intros F V ge k m [DOMAIN IMAGE] LE.
  exists (Genv.genv_next ge); split; auto. constructor; auto.
- intros; eapply Genv.genv_symb_range; eauto.
- intros b fd FIND. apply Genv.find_funct_ptr_iff in FIND.
  eapply Genv.genv_defs_range; eauto.
- intros b gv FIND. apply Genv.find_var_info_iff in FIND.
  eapply Genv.genv_defs_range; eauto.
Qed.

Lemma library_sep_globalenv:
  forall F V (ge: Genv.t F V) k m P Q,
  m |= P ** Q -> m |= globalenv_inject ge k ->
  m |= P ** Q ** globalenv_inject ge k.
Proof.
  intros F V ge k m P Q [HP [HQ DIS]] G.
  split; auto. split.
- split; auto. split; auto. red; simpl; tauto.
- red; simpl; intros b ofs A [B | B]; eauto.
Qed.

Lemma library_stacking_entry:
  forall p tp b fd saved sg m k ms sp,
  Stackingproof.match_prog p tp ->
  Genv.find_funct_ptr (Genv.globalenv p) b = Some fd -> Linear.funsig fd = sg ->
  Lineartyping.wt_locset saved ->
  (forall r, Val.inject k (saved (R r)) (ms r)) ->
  library_global_identity k (Genv.genv_next (Genv.globalenv p)) ->
  Ple (Genv.genv_next (Genv.globalenv p)) (Mem.nextblock m) ->
  m |= library_argument_area sg k sp saved ** minjection k m ->
  Lineartyping.wt_state
    (Linear.Callstate (Linear.ExternalFrame sg saved :: nil) fd saved m) /\
  Stackingproof.match_states Asmgenproof0.return_address_offset p tp
    (Linear.Callstate (Linear.ExternalFrame sg saved :: nil) fd saved m)
    (Mach.Callstate (Mach.ExternalFrame sp :: nil) b ms m).
Proof.
  intros p tp b fd saved sg m k ms sp PROG FIND SIG WT REG GLOBAL LE SEP.
  split.
- constructor; auto.
  + constructor; auto.
  + eapply Genv.find_funct_ptr_prop; [exact (Stackingproof.wt_prog p tp PROG) | exact FIND].
  + red; auto.
  + red; auto.
- destruct (Stackingproof.function_ptr_translated p tp PROG b fd FIND)
    as (tf & TFIND & TRANS).
  eapply Stackingproof.match_states_call with (j := k); eauto.
  + rewrite SIG. constructor. intros ofs ty IN.
    pose proof (loc_arguments_acceptable_2 sg _ IN) as ACCEPT.
    pose proof (loc_arguments_bounded sg ofs ty IN) as BOUND.
    simpl in ACCEPT. intuition lia.
  + eapply library_sep_globalenv; [exact SEP |].
    eapply library_globalenv_assertion; eauto.
Qed.

Lemma library_asmgen_entry:
  forall p tp id b sg args m ms sp rs,
  Asmgenproof.match_prog p tp ->
  Genv.find_symbol (Genv.globalenv p) id = Some b ->
  Asmgenproof0.agree ms (Vptr sp Ptrofs.zero) rs ->
  Asm.function_entry_state tp id sg args m (Asm.State rs m) ->
  Asmgenproof.match_states p
    (Mach.Callstate (Mach.ExternalFrame sp :: nil) b ms m) (Asm.State rs m).
Proof.
  intros p tp id b sg args m ms sp rs PROG SYM AG ENTRY.
  destruct ENTRY as (rs0 & tb & tf & tsp & EQ & TSYM & TFIND & PC & RA & SP & ARGS).
  inversion EQ; subst rs0.
  rewrite (Genv.find_symbol_match PROG) in TSYM. assert (tb = b) by congruence. subst tb.
  econstructor; eauto using Mem.extends_refl. constructor.
Qed.

(** Compilation constructs the full pass invariant from the public library ABI
    contract.  No intermediate compiler state is an assumption of this lemma. *)
Theorem library_entry_match:
  forall p tp id f args m rs tm,
  Compiler.transf_c_program p = Errors.OK tp ->
  In id p.(Ctypes.prog_public) ->
  (exists b, Genv.find_symbol (Csem.genv_genv (Csem.globalenv p)) id = Some b /\
     Genv.find_funct_ptr (Csem.genv_genv (Csem.globalenv p)) b = Some (Ctypes.Internal f)) ->
  SimplLocalsproof.val_casted_list args (Ctypes.type_of_params f.(Csyntax.fn_params)) ->
  Val.has_type_list args (proj_sig_args (function_signature f)) ->
  library_call p tp id (function_signature f) args m rs tm ->
  exists saved, function_match (function_signature f, saved)
    (p, Csem.Callstate (Ctypes.Internal f) args Csem.Kstop m) (tp, Asm.State rs tm).
Proof.
  intros p tp id f args m rs tm COMPILED PUBLIC (b & SYM & FIND) CAST TYPES CALL.
  destruct CALL as (initial & j & k & saved & ms & sp & actual_args &
    INIT & NEXT & CONSTANTS & NEUTRAL & SYMBOLS & MEM & ARGS & TTYPES & WT & REG & AG & GLOBAL & TLE & SEP & ENTRY).
  pose proof (library_flat_arguments _ _ _ _ _ MEM ARGS) as FLAT.
  pose proof (Genv.init_mem_genv_next _ INIT) as INITIAL_NEXT.
  assert (LE: Ple (Genv.genv_next (Genv.globalenv (Ctypes.program_of_program p))) (Mem.nextblock m)).
  { rewrite INITIAL_NEXT; exact NEXT. }
  pose proof (Compiler.transf_c_program_match p tp COMPILED) as M.
  unfold Compiler.match_prog, pass_match in M; simpl in M.
  destruct M as (p1 & M1 & M).
  destruct M as (p2 & M2 & M).
  destruct M as (p3 & M3 & M).
  destruct M as (p4 & M4 & M).
  destruct M as (p5 & M5 & M).
  destruct M as (p6 & M6 & M).
  destruct M as (p7 & M7 & M).
  destruct M as (p8 & M8 & M).
  destruct M as (p9 & M9 & M).
  destruct M as (p10 & M10 & M).
  destruct M as (p11 & M11 & M).
  destruct M as (p12 & M12 & M).
  destruct M as (p13 & M13 & M).
  destruct M as (p14 & M14 & M).
  destruct M as (p15 & M15 & M).
  destruct M as (p16 & M16 & M).
  destruct M as (p17 & M17 & M).
  destruct M as (p18 & M18 & M).
  destruct M as (p19 & M19 & M).
  destruct M as (p20 & M20 & M).
  destruct M as (p21 & M21 & M).
  subst p21.
  pose proof (library_match_layout _ _ _ _ _ (proj1 M1)) as L1.
  pose proof (library_match_layout _ _ _ _ _ (proj1 M2)) as L2.
  pose proof (library_match_layout _ _ _ _ _ M3) as L3.
  pose proof (library_match_layout _ _ _ _ _ M4) as L4.
  pose proof (library_match_layout _ _ _ _ _ M5) as L5.
  pose proof (library_match_layout _ _ _ _ _ M6) as L6.
  assert (L7: library_layout p6 p7).
  { eapply library_optional_layout; [apply library_layout_refl | | exact M7].
    intros x y H; exact (library_match_layout _ _ _ _ _ H). }
  pose proof (library_match_layout _ _ _ _ _ M8) as L8.
  pose proof (library_match_layout _ _ _ _ _ M9) as L9.
  assert (L10: library_layout p9 p10).
  { eapply library_optional_layout; [apply library_layout_refl | | exact M10].
    intros x y H; exact (library_match_layout _ _ _ _ _ H). }
  assert (L11: library_layout p10 p11).
  { eapply library_optional_layout; [apply library_layout_refl | | exact M11].
    intros x y H; exact (library_match_layout _ _ _ _ _ H). }
  assert (L12: library_layout p11 p12).
  { eapply library_optional_layout; [apply library_layout_refl | | exact M12].
    intros x y H; exact (library_match_layout _ _ _ _ _ H). }
  assert (L13: library_layout p12 p13).
  { eapply library_optional_layout; [apply library_layout_refl | | exact M13].
    intros x y H; exact (library_match_layout _ _ _ _ _ H). }
  pose proof (library_match_layout _ _ _ _ _ M15) as L15.
  pose proof (library_match_layout _ _ _ _ _ M16) as L16.
  pose proof (library_match_layout _ _ _ _ _ M17) as L17.
  pose proof (library_match_layout _ _ _ _ _ M18) as L18.
  assert (L19: library_layout p18 p19).
  { eapply library_optional_layout; [apply library_layout_refl | | exact M19].
    intros x y H; exact (library_match_layout _ _ _ _ _ H). }
  pose proof (library_match_layout _ _ _ _ _ M20) as L20.
  pose proof (library_match_layout _ _ _ _ _ M21) as L21.
  pose proof L1 as B1.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B1 L2) as B2.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B2 L3) as B3.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B3 L4) as B4.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B4 L5) as B5.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B5 L6) as B6.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B6 L7) as B7.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B7 L8) as B8.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B8 L9) as B9.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B9 L10) as B10.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B10 L11) as B11.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B11 L12) as B12.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ B12 L13) as B13.
  destruct B1 as [SYM1 [N1 [INIT1 PUB1]]].
  destruct B2 as [SYM2 [N2 [INIT2 PUB2]]].
  destruct B3 as [SYM3 [N3 [INIT3 PUB3]]].
  destruct B4 as [SYM4 [N4 [INIT4 PUB4]]].
  destruct B5 as [SYM5 [N5 [INIT5 PUB5]]].
  destruct B6 as [SYM6 [N6 [INIT6 PUB6]]].
  destruct B7 as [SYM7 [N7 [INIT7 PUB7]]].
  destruct B8 as [SYM8 [N8 [INIT8 PUB8]]].
  destruct B9 as [SYM9 [N9 [INIT9 PUB9]]].
  destruct B10 as [SYM10 [N10 [INIT10 PUB10]]].
  destruct B11 as [SYM11 [N11 [INIT11 PUB11]]].
  destruct B12 as [SYM12 [N12 [INIT12 PUB12]]].
  destruct B13 as [SYM13 [N13 [INIT13 PUB13]]].
  pose proof L21 as T20.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ L20 T20) as T19.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ L19 T19) as T18.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ L18 T18) as T17.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ L17 T17) as T16.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ L16 T16) as T15.
  pose proof (library_layout_trans _ _ _ _ _ _ _ _ _ L15 T15) as T14.
  destruct T14 as [TSYM14 [TN14 [TINIT14 TPUB14]]].
  destruct T19 as [TSYM19 [TN19 [TINIT19 TPUB19]]].
  destruct ENTRY as (rs0 & tb & af & asp & EQ & TSYM & AFIND & PC & RA & SP & ACTUAL).
  inversion EQ; subst rs0.
  assert (ENTRY: Asm.function_entry_state tp id (function_signature f) actual_args tm (Asm.State rs tm)).
  { exists rs, tb, af, asp; repeat split; auto. }
  assert (SIGNATURE: Csyntax.type_of_fundef (Ctypes.Internal f) =
    Ctypes.Tfunction (Ctypes.type_of_params f.(Csyntax.fn_params)) f.(Csyntax.fn_return) f.(Csyntax.fn_callconv)) by reflexivity.
  destruct (library_simpl_expr_entry _ _ _ _ args m M1 FIND) as (fd1 & F1 & S1 & R1).
  destruct (library_simpl_locals_entry _ _ _ _ args m _ _ _ M2 F1
    (eq_trans S1 SIGNATURE) CAST) as (fd2 & F2 & S2 & R2); auto.
  { exact (eq_ind_r (fun n => Ple n (Mem.nextblock m)) LE N1). }
  destruct (library_cshmgen_entry _ _ _ _ args m _ _ _ M3 F2
    (eq_trans S2 (eq_trans S1 SIGNATURE)) (library_cast_arguments _ _ CAST))
    as (fd3 & F3 & S3 & R3).
  change (Csharpminor.funsig fd3 = function_signature f) in S3.
  destruct (library_cminorgen_entry _ _ _ _ args m M4 F3) as (fd4 & F4 & S4 & R4); auto.
  { rewrite N3; exact LE. }
  destruct (library_selection_entry _ _ _ _ args m M5 F4) as (fd5 & F5 & S5 & R5).
  { rewrite S4, S3; exact TYPES. }
  destruct (library_rtlgen_entry _ _ _ _ args m M6 F5) as (fd6 & F6 & S6 & R6).
  destruct (library_optional_rtl_entry _ _ (fun _ _ => Tailcallproof.match_states)
    _ _ _ _ args m M7 F6) as (fd7 & F7 & S7 & R7).
  { intros H b0 fd H0; eapply library_tailcall_entry; eauto. }
  destruct (library_inlining_entry _ _ _ _ args m M8 F7) as (fd8 & F8 & S8 & R8); auto.
  { rewrite N7; exact LE. }
  destruct (library_renumber_entry _ _ _ _ args m M9 F8) as (fd9 & F9 & S9 & R9).
  destruct (library_optional_rtl_entry _ _
    (fun p _ s ts => ValueAnalysis.sound_state p s /\ exists n, Constpropproof.match_states p n s ts)
    _ _ _ _ args m M10 F9) as (fd10 & F10 & S10 & R10).
  { intros H b0 fd H0; eapply library_constprop_entry; eauto.
    eapply library_sound_call; eauto. }
  destruct (library_optional_rtl_entry _ _ (fun _ _ => Renumberproof.match_states)
    _ _ _ _ args m M11 F10) as (fd11 & F11 & S11 & R11).
  { intros H b0 fd H0; eapply library_renumber_entry; eauto. }
  destruct (library_optional_rtl_entry _ _ (fun p _ => rtl_eventually p (CSEproof.match_states p))
    _ _ _ _ args m M12 F11) as (fd12 & F12 & S12 & R12).
  { intros H b0 fd H0; eapply library_cse_entry; eauto.
    eapply library_sound_call; eauto. }
  destruct (library_optional_rtl_entry _ _ (fun p _ => rtl_eventually p (Deadcodeproof.match_states p))
    _ _ _ _ args m M13 F12) as (fd13 & F13 & S13 & R13).
  { intros H b0 fd H0; eapply library_deadcode_entry; eauto.
    eapply library_sound_call; eauto. }
  destruct M14 as (used & VALID & PRUNED).
  assert (SYMBOLS14: library_symbols (Genv.globalenv p13) (Genv.globalenv p14) j).
  { eapply library_symbols_transport; [exact SYM13 | | exact N13 | | exact SYMBOLS].
    - intros x; symmetry; apply TSYM14.
    - symmetry; exact TN14. }
  destruct (library_unusedglob_entry _ _ _ _ id b tb fd13 args
    (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments (function_signature f))) m tm
    VALID PRUNED SYMBOLS14) as (F14 & R14).
  { rewrite PUB13; exact PUBLIC. }
  { rewrite SYM13; exact SYM. }
  { rewrite <- TSYM14; exact TSYM. }
  { exact F13. }
  { rewrite N13; exact LE. }
  { rewrite <- TN14; exact TLE. }
  { exact MEM. }
  { exact ARGS. }
  assert (SIG13: RTL.funsig fd13 = function_signature f).
  { rewrite S13, S12, S11, S10, S9, S8, S7, S6, S5, S4, S3; reflexivity. }
  destruct (library_allocation_entry _ _ _ _ saved _ tm M15 F14 SIG13 TTYPES)
    as (fd15 & F15 & S15 & R15).
  destruct (library_tunneling_entry _ _ _ _ saved _ tm M16 F15 S15)
    as (fd16 & F16 & S16 & R16).
  destruct (library_linearize_entry _ _ _ _ saved _ tm M17 F16 S16)
    as (fd17 & F17 & S17 & R17).
  destruct (library_cleanup_entry _ _ _ _ saved _ tm M18 F17 S17)
    as (fd18 & F18 & S18 & R18).
  destruct (library_debug_entry _ _ _ _ saved _ tm M19 F18 S18)
    as (fd19 & F19 & S19 & R19).
  pose proof (library_stacking_entry _ _ _ _ saved _ tm k ms sp M20 F19 S19 WT REG) as R20.
  assert (R20': Lineartyping.wt_state
    (Linear.Callstate (Linear.ExternalFrame (function_signature f) saved :: nil) fd19 saved tm) /\
    Stackingproof.match_states Asmgenproof0.return_address_offset p19 p20
    (Linear.Callstate (Linear.ExternalFrame (function_signature f) saved :: nil) fd19 saved tm)
    (Mach.Callstate (Mach.ExternalFrame sp :: nil) tb ms tm)).
  { apply R20; [rewrite <- TN19; exact GLOBAL | rewrite <- TN19; exact TLE | exact SEP]. }
  assert (R21: Asmgenproof.match_states p20
    (Mach.Callstate (Mach.ExternalFrame sp :: nil) tb ms tm) (Asm.State rs tm)).
  { eapply library_asmgen_entry; eauto. rewrite <- (proj1 L21); exact TSYM. }
  exists saved.
  unfold function_match, clight_match, cminor_match, rtl_match, compose_match.
  exists (p1, Clight.Callstate fd1 args Clight.Kstop m); split.
  { split; [exact M1 | exact R1]. }
  exists (p2, Clight.Callstate fd2 args Clight.Kstop m); split.
  { split; [exact M2 | exact R2]. }
  exists (p3, Csharpminor.Callstate fd3 args Csharpminor.Kstop m); split.
  { split; [exact M3 | exact R3]. }
  exists (p4, Cminor.Callstate fd4 args Cminor.Kstop m); split.
  { split; [exact M4 | exact R4]. }
  exists (p5, CminorSel.Callstate fd5 args CminorSel.Kstop m); split.
  { split; [exact M5 | exact R5]. }
  exists (p6, RTL.Callstate nil fd6 args m); split.
  { split; [exact M6 | exact R6]. }
  exists (p7, RTL.Callstate nil fd7 args m); split.
  { exact R7. }
  exists (p8, RTL.Callstate nil fd8 args m); split.
  { split; [exact M8 | exact R8]. }
  exists (p9, RTL.Callstate nil fd9 args m); split.
  { split; [exact M9 | exact R9]. }
  exists (p10, RTL.Callstate nil fd10 args m); split.
  { exact R10. }
  exists (p11, RTL.Callstate nil fd11 args m); split.
  { exact R11. }
  exists (p12, RTL.Callstate nil fd12 args m); split.
  { exact R12. }
  exists (p13, RTL.Callstate nil fd13 args m); split.
  { exact R13. }
  exists (p14, RTL.Callstate nil fd13 (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments (function_signature f))) tm); split.
  { split; [exists used; auto | exists used; auto]. }
  exists (p15, LTL.Callstate (LTL.ExternalFrame (function_signature f) saved :: nil) fd15 saved tm); split.
  { split; [exact M15 | exact R15]. }
  exists (p16, LTL.Callstate (LTL.ExternalFrame (function_signature f) saved :: nil) fd16 saved tm); split.
  { split; [exact M16 | exact R16]. }
  exists (p17, Linear.Callstate (Linear.ExternalFrame (function_signature f) saved :: nil) fd17 saved tm); split.
  { split; [exact M17 | exact R17]. }
  exists (p18, Linear.Callstate (Linear.ExternalFrame (function_signature f) saved :: nil) fd18 saved tm); split.
  { split; [exact M18 | exact R18]. }
  exists (p19, Linear.Callstate (Linear.ExternalFrame (function_signature f) saved :: nil) fd19 saved tm); split.
  { exact R19. }
  exists (p20, Mach.Callstate (Mach.ExternalFrame sp :: nil) tb ms tm); split.
  { split; [exact M20 | exact R20']. }
  split; [exact M21 | exact R21].
Qed.

(** A terminating call to an exported library function compiles to a finite
    assembly execution with the same trace and a related ABI result and heap.
    The entry premises concern only source values, memory, symbols, and the ABI. *)
Theorem transf_c_function_correct:
  forall p tp id f args m rs tm t v m',
  Compiler.transf_c_program p = Errors.OK tp ->
  In id p.(Ctypes.prog_public) ->
  (exists b, Genv.find_symbol (Csem.genv_genv (Csem.globalenv p)) id = Some b /\
     Genv.find_funct_ptr (Csem.genv_genv (Csem.globalenv p)) b = Some (Ctypes.Internal f)) ->
  SimplLocalsproof.val_casted_list args (Ctypes.type_of_params f.(Csyntax.fn_params)) ->
  Val.has_type_list args (proj_sig_args (function_signature f)) ->
  library_call p tp id (function_signature f) args m rs tm ->
  star Cstrategy.step (Csem.globalenv p)
    (Csem.Callstate (Ctypes.Internal f) args Csem.Kstop m) t
    (Csem.Returnstate v Csem.Kstop m') ->
  exists rs' tm',
    star Asm.step (Genv.globalenv tp) (Asm.State rs tm) t (Asm.State rs' tm') /\
    rs' Asm.PC = Vnullptr /\
    value_memory_match v m' (asm_result (function_signature f) rs') tm'.
Proof.
  intros p tp id f args m rs tm t v m' COMPILED PUBLIC FIND CAST TYPES CALL RUN.
  destruct (library_entry_match _ _ _ _ _ _ _ _ COMPILED PUBLIC FIND CAST TYPES CALL)
    as (saved & MATCH).
  destruct (function_match_execution (function_signature f, saved)
    _ _ _ _ _ _ MATCH (program_star _ _ _ _ _ _ _ _ _ RUN))
    as (ast' & TRUN & MATCH').
  destruct (function_match_return (function_signature f) saved
    _ _ _ _ _ _ MATCH' eq_refl) as (tv & tm' & [rs' [EQ [PC RES]]] & RESULT).
  subst ast' tv. exists rs', tm'; split; [|auto].
  eapply program_star_inv; exact TRUN.
Qed.
