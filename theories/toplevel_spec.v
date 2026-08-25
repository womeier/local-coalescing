(** Top-level correctness specification for the local-coalescing pass.

    This file states the property, and nothing else: the [Prop]-valued
    [Definition]s here are what a consumer reads.  Keeping them in their own
    file kept the goalposts fixed while the proof was built up towards them.

    It is now discharged.  [coalesce_module_correct_statement], at the
    bottom of this file, is the type of [coalesce_module_correct] in
    toplevel_correct.v verbatim -- hypotheses included, written out in one
    piece.  Reading it is reading what has been proved; nothing has to be
    assembled from the proof files.

    [coalesce_module_correct_spec] is kept as the idealised goal, the
    statement with no hypotheses at all.  The two differ by exactly the two
    hypotheses, each documented where it is defined.

    Design constraints the statement deliberately satisfies:

    - It mentions [coalesce_module], the actual entry point of the pass, and
      nothing else pass-specific.  In particular the rename map [phi], the
      agreement relation [R_phi] / [R_phi_live], the per-frame relation and
      the store relation are all *internal* to the eventual proof and do not
      appear here.  A consumer should not have to know the pass exists beyond
      naming it.

    - It is an equivalence, not a one-way simulation.  [apply_phi] is
      shape-preserving and lockstep, so both directions should be provable,
      and a consumer can then use whichever half it needs.  (Backward
      simulation alone does not yield the forward direction without a
      progress argument, and WasmCert's semantics is not determinate:
      [host_application] is a relation -- see host.v:33.)

    - It is phrased so that it composes with CertiRocq's
      [theories/CodegenWasm/toplevel_theorem.v], whose [LambdaANF_Wasm_related]
      runs the program from [Build_frame [] (f_inst fr)] with
      [AI_basic (BI_call main_function_idx)] after [instantiate].

    The three obligations this statement forces, and where each is discharged:

    1. Type preservation.  [instantiate] carries [module_typing m _ _] as a
       conjunct, so producing an instantiation of [coalesce_module m] requires
       the coalesced module to validate.  Merging two locals of different
       value types onto one slot would break that, since [apply_phi_func]
       leaves [modfunc_locals] unchanged and a slot keeps its originally
       declared type.  Slot selection is type-aware and [module_supported]
       accepts only all-i32 locals; [module_typing_coalesce]
       (instantiation.v) is the result.

    2. Instantiation preservation.  The pass touches only [modfunc_body],
       leaving [modfunc_type], [modfunc_locals], globals, elems, datas, start
       and exports alone, so allocation proceeds identically --
       [alloc_module_coalesce], and [coalesce_instantiate] above it
       (instantiation.v).

    3. Call equivalence.  The per-frame, liveness-keyed simulation, in both
       directions: [sim_step_store] and [sim_step_store_bwd], closed under
       [reduce_trans] and glued together by [call_equiv_from_store_rel]
       (toplevel_correct.v).  See the notes on [R_phi_live] in
       coalesce_locals_correct.v for why agreement must be restricted to live
       locals rather than stated for all of them.
*)

From Wasm Require Import datatypes opsem instantiation_spec.
From Stdlib Require Import List.
From Wasmopt Require Import coalesce_locals.

Import ListNotations.

Section TopLevelSpec.

Context `{hfc : host_function_class} `{memory : BlockUpdateMemory} `{ho : host}.

(** A finished thread: a value stack or a trap.  Stated here rather than
    reused from [operations.terminal_form] so that the specification is
    self-contained and says what a consumer wants to read off -- [res] *is* a
    list of values -- rather than "every element satisfies [is_const]". *)
Definition terminal (res : list administrative_instruction) : Prop :=
  (exists rvs, res = v_to_e_list rvs) \/ res = [AI_trap].

(** The two stores can never be equal: [s_funcs] holds the code, and on the
    optimized side it holds the coalesced bodies -- that is the point of the
    pass.  So the relation between the final stores is equality on everything
    a program can observe, and nothing about the code.

    Leaving the final stores unrelated instead (two independent existentials)
    would be much too weak: the equivalence would constrain only the returned
    value stack, and a pass that scribbled over linear memory would satisfy
    it.  Memory and globals are the point; tables, elems and datas are equal
    for the same reason and cost nothing to state. *)
Definition store_visible_eq (s s_opt : store_record) : Prop :=
  s_tables  s = s_tables  s_opt /\
  s_mems    s = s_mems    s_opt /\
  s_globals s = s_globals s_opt /\
  s_elems   s = s_elems   s_opt /\
  s_datas   s = s_datas   s_opt.

(** Calling function address [a] with arguments [vs] behaves the same in the
    two stores: whichever side reaches a finished thread [res], the other
    reaches the same [res], with the same host state and a visibly equal
    store.

    [res] must be restricted to [terminal] -- a value stack or a trap.
    That is not cosmetic.  Quantified over an arbitrary
    [list administrative_instruction], [res] would range over *intermediate*
    configurations too, and those necessarily differ between the two runs:
    they carry the code being executed inside [AI_frame]/[AI_label], which is
    coalesced on one side and not on the other.  A source run reaching
    [AI_frame m fr [AI_label m [] (to_e_list [local.set 2; local.get 2])]] has
    no counterpart in a store whose code says [local.set 0], so the
    unrestricted statement is unprovable exactly when the pass does something.
    A terminal [res] mentions no locals and no code, which is what lets the
    rename map and the agreement relation stay out of the statement.

    Stated as two implications rather than an [iff] so that each direction can
    relate the *same* pair of final stores; an [iff] between two existentials
    cannot say anything about the two witnesses.

    [hs'] is shared between the two sides deliberately: it pins the host's
    nondeterministic choices, which matters because [host_application] is a
    relation (host.v:33) rather than a function. *)
Definition call_equiv (s s_opt : store_record) (f f_opt : frame) : Prop :=
  forall (a : funcaddr) (vs : list value) (hs hs' : host_state)
         (res : list administrative_instruction),
    terminal res ->
    (forall s',
       reduce_trans (hs, s, f, v_to_e_list vs ++ [AI_invoke a])
                    (hs', s', f, res) ->
       exists s_opt',
         reduce_trans (hs, s_opt, f_opt, v_to_e_list vs ++ [AI_invoke a])
                      (hs', s_opt', f_opt, res) /\
         store_visible_eq s' s_opt')
    /\
    (forall s_opt',
       reduce_trans (hs, s_opt, f_opt, v_to_e_list vs ++ [AI_invoke a])
                    (hs', s_opt', f_opt, res) ->
       exists s',
         reduce_trans (hs, s, f, v_to_e_list vs ++ [AI_invoke a])
                      (hs', s', f, res) /\
         store_visible_eq s' s_opt').

Lemma store_visible_eq_sym : forall s s',
  store_visible_eq s s' -> store_visible_eq s' s.
Proof.
  intros s s' [Ht [Hm [Hg [He Hd]]]].
  repeat split; symmetry; assumption.
Qed.

(** The goal.  Whenever the source module instantiates, so does the coalesced
    module, and every call into the result behaves identically. *)
Definition coalesce_module_correct_spec : Prop :=
  forall (s : store_record) (m : module) (v_imps : list extern_value)
         (s_end : store_record) (f : frame) (bes : list basic_instruction),
    instantiate s m v_imps (s_end, f, bes) ->
    exists s_end_opt f_opt bes_opt,
      instantiate s (coalesce_module m) v_imps (s_end_opt, f_opt, bes_opt) /\
      call_equiv s_end s_end_opt f f_opt.

(** ── The two hypotheses the theorem carries ─────────────────────────────
    Both are stated here rather than in the proof, so that this file says
    exactly what is established and a consumer has one place to look.
    Neither mentions anything internal to the pass. *)

(** A host call may not look at the code section, nor change it.

    In WasmCert a call to an imported host function is an arbitrary
    *relation* ([host_application], host.v:33) that may return any store at
    all.  Nothing in the semantics stops a host from reading the function
    bodies in the store and behaving differently once a callee's locals have
    been renamed, and no proof about the Wasm side can rule that out.  This
    says it does not: run against two stores that agree on everything but
    their code, a host call has the same outcomes, and leaves each store's
    code alone.

    [s_funcs s1' = s_funcs s1] is the "installs no Wasm code of its own"
    half.  A host that did install code would have to install *related* code
    on both sides to keep the simulation going, which is not something an
    embedder can be asked to promise. *)
Definition host_ignores_code : Prop :=
  (forall hs s1 s2 tf h vcs hs' r s1',
     store_visible_eq s1 s2 ->
     host_application hs s1 tf h vcs hs' (Some (s1', r)) ->
     exists s2', host_application hs s2 tf h vcs hs' (Some (s2', r))
              /\ store_visible_eq s1' s2'
              /\ s_funcs s1' = s_funcs s1
              /\ s_funcs s2' = s_funcs s2)
  /\
  (forall hs s1 s2 tf h vcs hs',
     store_visible_eq s1 s2 ->
     host_application hs s1 tf h vcs hs' None ->
     host_application hs s2 tf h vcs hs' None).

(** Every Wasm function already in the store obeys the nesting restriction
    the pass checks on the code it compiles.

    The store being instantiated into may already hold function instances --
    imports, or earlier instantiations.  Those are the *same* on both sides,
    so the simulation still has to relate each of them to itself, and doing
    that needs the restriction.  The pass only ever sees the module it is
    handed, so it cannot check this, and it has to be assumed.

    It is vacuous when the store holds only host functions, since it
    constrains [FC_func_native] alone -- which is the CertiRocq setting. *)
Definition store_guarded (s : store_record) : Prop :=
  forall addr tf inst code,
    lookup_N (s_funcs s) addr = Some (FC_func_native tf inst code) ->
    bs_guarded (modfunc_body code) = true.

(** ── The statement that is proved ───────────────────────────────────────
    This, verbatim, is the type of [coalesce_module_correct] in
    toplevel_correct.v.  It is written out in one piece rather than layered
    on [coalesce_module_correct_spec], so that everything the theorem
    assumes is visible in the place where it is assumed: the host condition
    in front, the store condition on [s].

    It differs from [coalesce_module_correct_spec] above by exactly those
    two hypotheses, and in nothing else. *)
Definition coalesce_module_correct_statement : Prop :=
  host_ignores_code ->
  forall (s : store_record) (m : module) (v_imps : list extern_value)
         (s_end : store_record) (f : frame) (bes : list basic_instruction),
    store_guarded s ->
    instantiate s m v_imps (s_end, f, bes) ->
    exists s_end_opt f_opt bes_opt,
      instantiate s (coalesce_module m) v_imps (s_end_opt, f_opt, bes_opt) /\
      call_equiv s_end s_end_opt f f_opt.

End TopLevelSpec.
