(** Regression checks for the general-signature library boundary. *)
Require Import Coqlib AST Values Memory Locations Conventions.
Require Import Cminor Cminortyping RTL RTLtyping LTL Linear Mach Allocproof Stackingproof.
Require Import FunctionSpec LibrarySpec Libraryproof.

(** No integer-result or register-only restriction is needed at the boundary. *)
Lemma all_signatures_have_external_callers:
  forall lp mp sg saved sp j,
  Cminortyping.wt_cont_call Cminor.Kstop sg.(sig_res) /\
  RTLtyping.wt_stackframes nil sg /\
  Allocproof.match_stackframes lp (Some (sg, saved)) nil
    (LTL.ExternalFrame sg saved :: nil) sg /\
  Stackingproof.match_stacks mp j (Linear.ExternalFrame sg saved :: nil)
    (Mach.ExternalFrame sp :: nil) sg.
Proof.
  intros lp mp sg saved sp j.
  split; [constructor |]. split; [constructor |]. split.
- econstructor; reflexivity.
- econstructor. intros ofs ty ARGS.
  pose proof (loc_arguments_acceptable_2 sg (S Outgoing ofs ty) ARGS) as [LO ALIGN].
  assert (NONNEG: 0 <= ofs) by lia.
  exact (conj NONNEG (conj (loc_arguments_bounded sg ofs ty ARGS) ALIGN)).
Qed.

(** Twenty integer arguments force the configured ABI to use stack slots,
    while the result uses the floating-point calling convention. *)
Definition stack_signature := mksignature (List.repeat Xint 20) Xfloat cc_default.

Example signature_has_stack_arguments: size_arguments stack_signature > 0.
Proof.
  vm_compute.
  repeat match goal with |- context [if ?flag then _ else _] => destruct flag end;
    vm_compute; reflexivity.
Qed.

Example floating_result_boundary:
  forall lp saved, Allocproof.match_stackframes lp (Some (stack_signature, saved)) nil
    (LTL.ExternalFrame stack_signature saved :: nil) stack_signature.
Proof. intros; constructor; reflexivity. Qed.

Example void_result_boundary:
  forall lp saved, let sg := mksignature nil Xvoid cc_default in
  Allocproof.match_stackframes lp (Some (sg, saved)) nil
    (LTL.ExternalFrame sg saved :: nil) sg.
Proof. intros; constructor; reflexivity. Qed.

Check transf_c_function_correct.
