(** * Public entry conditions for a standalone library function.
    These conditions describe initialized constants, caller-owned memory,
    global-address relocation, and ABI arguments.  They contain no compiler
    state relations and no assumption about an assembly execution. *)

Require Import Coqlib AST Values Memory Globalenvs Events Locations Conventions.
Require Import Separation FunctionSpec.
Require Stackingproof Asmgenproof0 Lineartyping.

(** Preserve initially read-only blocks while allowing mutable globals and newly
    allocated caller data to change.  Permissions on constant blocks cannot grow. *)
Definition library_constants (initial current: Mem.mem) : Prop :=
  forall b,
  Mem.valid_block initial b ->
  (forall ofs, ~Mem.perm initial b ofs Max Writable) ->
  (forall ofs n bytes, Mem.loadbytes current b ofs n = Some bytes ->
     Mem.loadbytes initial b ofs n = Some bytes) /\
  (forall ofs perm, Mem.perm current b ofs Max perm ->
     Mem.perm initial b ofs Max perm).

(** Global addresses are relocated by symbol name.  Heap blocks cannot turn
    into globals, and every symbol present in both images is mapped. *)
Record library_symbols {F V TF TV: Type}
    (ge: Genv.t F V) (tge: Genv.t TF TV) (j: meminj) : Prop := {
  library_source_global:
    forall b tb delta, j b = Some (tb, delta) -> Plt b (Genv.genv_next ge) ->
    exists id, Genv.find_symbol ge id = Some b /\
               Genv.find_symbol tge id = Some tb /\ delta = 0;
  library_target_global:
    forall b tb delta, j b = Some (tb, delta) -> Plt tb (Genv.genv_next tge) ->
    exists id, Genv.find_symbol ge id = Some b /\
               Genv.find_symbol tge id = Some tb /\ delta = 0;
  library_common_symbol:
    forall id b tb, Genv.find_symbol ge id = Some b ->
    Genv.find_symbol tge id = Some tb -> j b = Some (tb, 0)
}.

(** The second injection preserves the target's global-address area.  It may
    omit the caller's argument block, which belongs to the caller rather than
    the library's source-visible memory. *)
Definition library_global_identity (j: meminj) (bound: block) : Prop :=
  (forall b, Plt b bound -> j b = Some (b, 0)) /\
  (forall b tb delta, j b = Some (tb, delta) -> Plt tb bound -> b = tb).

Local Open Scope sep_scope.

(** The caller's ABI argument slots occupy a separate, aligned memory area.
    The empty-program parameter of the existing assertion occurs only in its
    proof fields, not in its memory predicate or footprint. *)
Definition library_argument_area (sg: signature) (k: meminj)
    (sp: block) (saved: LTL.locset) : massert :=
  Stackingproof.contains_locations Asmgenproof0.return_address_offset
    (AST.mkprogram nil nil 1%positive) k sp Stacklayout.fe_ofs_arg
    (size_arguments sg) Outgoing saved.

(** A library call supplies a source heap, a physical heap and register state,
    and a typed logical view of ABI locations.  Constant globals keep their
    initial values; writable globals and caller allocations need not do so. *)
Definition library_call (p: Csyntax.program) (tp: Asm.program)
    (id: ident) (sg: signature) (args: list val) (m: Mem.mem)
    (rs: Asm.regset) (tm: Mem.mem) : Prop :=
  exists initial j k saved ms sp actual_args,
    Genv.init_mem (Ctypes.program_of_program p) = Some initial /\
    Ple (Mem.nextblock initial) (Mem.nextblock m) /\
    library_constants initial m /\
    Mem.inject_neutral (Mem.nextblock m) m /\
    library_symbols (Csem.genv_genv (Csem.globalenv p)) (Genv.globalenv tp) j /\
    Mem.inject j m tm /\
    Val.inject_list j args
      (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments sg)) /\
    Val.has_type_list
      (List.map (fun loc => Locmap.getpair loc saved) (loc_arguments sg))
      (proj_sig_args sg) /\
    Lineartyping.wt_locset saved /\
    (forall r, Val.inject k (saved (R r)) (ms r)) /\
    Asmgenproof0.agree ms (Vptr sp Integers.Ptrofs.zero) rs /\
    library_global_identity k (Genv.genv_next (Genv.globalenv tp)) /\
    Ple (Genv.genv_next (Genv.globalenv tp)) (Mem.nextblock tm) /\
    tm |= library_argument_area sg k sp saved ** minjection k tm /\
    Asm.function_entry_state tp id sg actual_args tm (Asm.State rs tm).
