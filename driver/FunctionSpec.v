(** * State relations for fresh function calls through the CompCert pipeline.
    These are the existing pass invariants, including typing, value-analysis,
    and memory conditions.  They do not assume an execution or its result.

    The external caller has a general signature and a caller-owned argument
    area.  Its frame is a boundary marker, not executable compiler code. *)

Require Import Coqlib AST Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions.
Require Import Compiler.
Require Cminortyping RTLtyping Lineartyping ValueAnalysis.

(** Combine a pass's program relation with its concrete execution-state relation. *)
Definition match_pass {P Q S T: Type}
    (programs: P -> Q -> Prop) (states: P -> Q -> S -> T -> Prop)
    (x: P * S) (y: Q * T) : Prop :=
  programs (fst x) (fst y) /\ states (fst x) (fst y) (snd x) (snd y).

(** Two configurations match through consecutive passes when an intermediate
    program and execution state satisfy both pass relations. *)
Definition compose_match {A B C: Type}
    (R: A -> B -> Prop) (S: B -> C -> Prop) (x: A) (z: C) : Prop :=
  exists y, R x y /\ S y z.

Notation "R >>> S" := (compose_match R S)
  (at level 60, right associativity).

(** A disabled optional pass preserves both the program and its execution state. *)
Definition optional_match {A: Type} (flag: unit -> bool)
    (R: A -> A -> Prop) (x y: A) : Prop :=
  if flag tt then R x y else x = y.

(** Instruction selection can advance over a finite sequence of source steps.
    It must stop at every return from the fresh call, regardless of value type. *)
Definition selection_states (p: Cminor.program)
    (s: Cminor.state) (ts: CminorSel.state) : Prop :=
  exists n, Smallstep.eventually Cminor.step Cminor.function_final_state
    (Genv.globalenv p) n s
    (fun s' => Selectionproof.match_states p s' ts /\ Cminortyping.wt_state s').

(** Value numbering and dead-code elimination can also advance the source.
    Their state relation includes the value-analysis invariant at the match. *)
Definition rtl_eventually (p: RTL.program)
    (R: RTL.state -> RTL.state -> Prop) (s ts: RTL.state) : Prop :=
  exists n, Smallstep.eventually RTL.step RTL.function_final_state
    (Genv.globalenv p) n s
    (fun s' => R s' ts /\ ValueAnalysis.sound_state p s').

(** This relation records every pass of RTL-to-assembly compilation, including
    the concrete witnesses for eliminated globals and all analysis invariants. *)
Definition rtl_match (caller: signature * LTL.locset) :
    RTL.program * RTL.state -> Asm.program * Asm.state -> Prop :=
  optional_match Compopts.optim_tailcalls
    (match_pass Tailcallproof.match_prog (fun _ _ => Tailcallproof.match_states)) >>>
  match_pass Inliningproof.match_prog (fun p _ => Inliningproof.match_states p) >>>
  match_pass Renumberproof.match_prog (fun _ _ => Renumberproof.match_states) >>>
  optional_match Compopts.optim_constprop
    (match_pass Constpropproof.match_prog
      (fun p _ s ts => ValueAnalysis.sound_state p s /\
                      exists n, Constpropproof.match_states p n s ts)) >>>
  optional_match Compopts.optim_constprop
    (match_pass Renumberproof.match_prog (fun _ _ => Renumberproof.match_states)) >>>
  optional_match Compopts.optim_CSE
    (match_pass CSEproof.match_prog (fun p _ => rtl_eventually p (CSEproof.match_states p))) >>>
  optional_match Compopts.optim_redundancy
    (match_pass Deadcodeproof.match_prog (fun p _ => rtl_eventually p (Deadcodeproof.match_states p))) >>>
  match_pass Unusedglobproof.match_prog
    (fun p tp s ts => exists used,
       Unusedglobproof.valid_used_set p used /\
       Unusedglobproof.match_prog_1 used p tp /\
       Unusedglobproof.match_states p tp used s ts) >>>
  match_pass Allocproof.match_prog
    (fun _ tp s ts => RTLtyping.wt_state s /\ Allocproof.match_states tp (Some caller) s ts) >>>
  match_pass Tunnelingproof.match_prog (fun _ _ => Tunnelingproof.match_states) >>>
  match_pass Linearizeproof.match_prog (fun _ _ => Linearizeproof.match_states) >>>
  match_pass CleanupLabelsproof.match_prog (fun _ _ => CleanupLabelsproof.match_states) >>>
  optional_match Compopts.debug
    (match_pass Debugvarproof.match_prog (fun _ _ => Debugvarproof.match_states)) >>>
  match_pass Stackingproof.match_prog
    (fun p tp s ts => Lineartyping.wt_state s /\
       Stackingproof.match_states Asmgenproof0.return_address_offset p tp s ts) >>>
  match_pass Asmgenproof.match_prog (fun p _ => Asmgenproof.match_states p).

(** Cminor-to-assembly matching prepends instruction selection and RTL generation. *)
Definition cminor_match (caller: signature * LTL.locset) :
    Cminor.program * Cminor.state -> Asm.program * Asm.state -> Prop :=
  match_pass Selectionproof.match_prog (fun p _ => selection_states p) >>>
  match_pass RTLgenproof.match_prog (fun _ _ => RTLgenproof.match_states) >>>
  rtl_match caller.

(** Clight-to-assembly matching includes the two distinct Clight semantics
    on either side of local-variable simplification. *)
Definition clight_match (caller: signature * LTL.locset) :
    Clight.program * Clight.state -> Asm.program * Asm.state -> Prop :=
  match_pass SimplLocalsproof.match_prog (fun p _ => SimplLocalsproof.match_states p) >>>
  match_pass Cshmgenproof.match_prog (fun p tp => Cshmgenproof.match_states p tp) >>>
  match_pass Cminorgenproof.match_prog (fun p _ => Cminorgenproof.match_states p) >>>
  cminor_match caller.

(** Source and assembly states match through the actual compiler passes.
    This concrete predicate is also the postcondition at a source return. *)
Definition function_match (caller: signature * LTL.locset) :
    Csyntax.program * Csem.state -> Asm.program * Asm.state -> Prop :=
  match_pass SimplExprproof.match_prog SimplExprproof.match_states >>> clight_match caller.

(** The calling convention uses the source function's declared parameter and
    result types, including pointer, floating-point, and void results. *)
Definition function_signature (f: Csyntax.function) : signature :=
  Ctypes.signature_of_type (Ctypes.type_of_params f.(Csyntax.fn_params))
    f.(Csyntax.fn_return) f.(Csyntax.fn_callconv).

(** Finite execution preservation keeps both programs fixed and preserves a
    concrete relation between execution states, without requiring [main]. *)
Definition execution_preserved {P Q S T: Type}
    (step: P -> S -> trace -> S -> Prop)
    (tstep: Q -> T -> trace -> T -> Prop)
    (R: P * S -> Q * T -> Prop) : Prop :=
  forall p tp s ts t s',
  R (p, s) (tp, ts) -> star step p s t s' ->
  exists ts', star tstep tp ts t ts' /\ R (p, s') (tp, ts').

(** Corresponding results either keep the same memory blocks and become more
    defined, or relocate blocks through a CompCert memory injection. *)
Definition value_memory_match (v: val) (m: Mem.mem) (tv: val) (tm: Mem.mem) : Prop :=
  (Val.lessdef v tv /\ Mem.extends m tm) \/
  exists j, Val.inject j v tv /\ Mem.inject j m tm.

(** Returns before register allocation carry an explicit value and memory. *)
Definition c_return (s: Csem.state) (v: val) (m: Mem.mem) : Prop :=
  s = Csem.Returnstate v Csem.Kstop m.
Definition clight_return (s: Clight.state) (v: val) (m: Mem.mem) : Prop :=
  s = Clight.Returnstate v Clight.Kstop m.
Definition csharpminor_return (s: Csharpminor.state) (v: val) (m: Mem.mem) : Prop :=
  s = Csharpminor.Returnstate v Csharpminor.Kstop m.
Definition cminor_return (s: Cminor.state) (v: val) (m: Mem.mem) : Prop :=
  s = Cminor.Returnstate v Cminor.Kstop m.
Definition cminorsel_return (s: CminorSel.state) (v: val) (m: Mem.mem) : Prop :=
  s = CminorSel.Returnstate v CminorSel.Kstop m.
Definition rtl_return (s: RTL.state) (v: val) (m: Mem.mem) : Prop :=
  s = RTL.Returnstate nil v m.

(** LTL and Linear return to a non-executable external caller frame.
    The signature selects the ABI result register or register pair. *)
Definition ltl_return (sg: signature) (s: LTL.state) (v: val) (m: Mem.mem) : Prop :=
  exists saved ls,
    s = LTL.Returnstate (LTL.ExternalFrame sg saved :: nil) ls m /\
    v = Locmap.getpair (map_rpair R (loc_result sg)) ls.
Definition linear_return (sg: signature) (s: Linear.state) (v: val) (m: Mem.mem) : Prop :=
  exists saved ls,
    s = Linear.Returnstate (Linear.ExternalFrame sg saved :: nil) ls m /\
    v = Locmap.getpair (map_rpair R (loc_result sg)) ls.

(** Read the result registers selected by the function signature in Mach. *)
Definition mach_result (sg: signature) (rs: Mach.regset) : val :=
  match loc_result sg with
  | One r => rs r
  | Twolong hi lo => Val.longofwords (rs hi) (rs lo)
  end.
Definition mach_return (sg: signature) (s: Mach.state) (v: val) (m: Mem.mem) : Prop :=
  exists sp rs,
    s = Mach.Returnstate (Mach.ExternalFrame sp :: nil) rs m /\
    v = mach_result sg rs.

(** Read the ABI result in assembly, including split 64-bit results. *)
Definition asm_result (sg: signature) (rs: Asm.regset) : val :=
  match Asm.loc_external_result sg with
  | One r => rs r
  | Twolong hi lo => Val.longofwords (rs hi) (rs lo)
  end.
Definition asm_return (sg: signature) (s: Asm.state) (v: val) (m: Mem.mem) : Prop :=
  exists rs, s = Asm.State rs m /\
    rs Asm.PC = Vnullptr /\ v = asm_result sg rs.

(** Each pass relates returns at the same caller boundary and preserves both
    the result and memory, independently of an execution's length. *)
Definition return_preserved {P Q S T: Type}
    (R: P * S -> Q * T -> Prop)
    (ret: S -> val -> Mem.mem -> Prop)
    (tret: T -> val -> Mem.mem -> Prop) : Prop :=
  forall p tp s ts v m,
  R (p, s) (tp, ts) -> ret s v m ->
  exists tv tm, tret ts tv tm /\ value_memory_match v m tv tm.
