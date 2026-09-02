(** The route from what is proved to [coalesce_module_correct_spec].

    Every statement the top-level theorem needs is written out here, and
    all of them are now proved: [Print Assumptions coalesce_module_correct]
    names only WasmCert's own axioms (classical reals via Flocq,
    functional extensionality, the SIMD op strings) and the three host
    assumptions collected in [host_ok], which are hypotheses of the
    theorem rather than axioms.

    What this file builds on:

    - [sim_step] (coalesce_locals_correct.v): one source step is matched
      by one optimized step, preserving [rel_es] and [frames_agree].
      Both sides run against the *same* store.
    - [coalesce_func_with_types_related] (alloc_correct.v): the body the
      pass emits is [rel_bs]-related to the original, at the map the
      pass computes.
    - [store_rel] and [coalesce_instantiate] (instantiation.v): what it
      means for two stores to be related, and that instantiating the
      coalesced module reaches the same instance and a related store.
      That file holds everything that never runs user code -- typing
      preservation, allocation, the initializer runs.

    What is proved here -- the half that runs code, and the assembly:

    - [sim_step_store] -- [sim_step] against a related pair of stores
       rather than one shared store.  This is what lets a call reach the
       *coalesced* callee: [r_invoke_native] enters the [code_opt] that
       [funcinst_rel] hands back, and the two activations are related at
       the callee's own map.  Its closure [sim_trans_store] and the
       [call_equiv] glue follow.
    - The backward simulation, [sim_step_store_bwd].  [call_equiv] is an
      equivalence, and WasmCert's semantics is not determinate
      ([host_application] is a relation), so this is a second induction
      rather than the forward one run backwards.  It reuses the whole
      [_r] inversion suite and the [with_funcs] normal form, with the
      source store in the [with_funcs] position instead of the
      optimized one.
    - Terminal transfer: a related pair of finished threads is an equal
       pair, in both directions.

    Three assumptions about the host appear below.  They are genuine --
    [host_application] may return any store at all -- and they are what
    a whole-program analysis needs of an embedder: it may not install
    Wasm code, and it may not behave differently because the code in the
    store was renamed.  CertiRocq's host satisfies all three. *)

From Wasm Require Import datatypes datatypes_properties opsem properties
                         typing instantiation_spec.
From Stdlib Require Import List Lia.
From Wasmopt Require Import coalesce_locals coalesce_locals_correct
                            alloc_correct toplevel_spec instantiation.

Import Bool ssreflect BinNat ListNotations.

Section TopLevelCorrect.

Context `{hfc : host_function_class} `{memory : BlockUpdateMemory} `{ho : host}.

(* ── 1. The optimized store is the source store with other code ───
   [store_rel], [funcinst_rel], [code_rel] and [with_funcs] are defined
   in instantiation.v, which is where a related store is built; this is
   the suite that says the *simulation* can carry one along.

   store_rel fixes every section but s_funcs, so [s_opt] *is*
   [with_funcs s (s_funcs s_opt)].  That is what makes the simulation's
   store side cheap: every rule that touches the store touches one of
   the equal sections and rebuilds the record leaving s_funcs alone, so
   each operation transfers verbatim, and the optimized successor store
   is the source successor store carrying the optimized code.

   The ten lemmas below are the ten store-changing operations
   [reduce] has.  They are all the same statement and all go through by
   the same reduction; only the argument lists differ. *)

Lemma store_rel_shape : forall s s_opt,
  store_rel s s_opt -> s_opt = with_funcs s (s_funcs s_opt).
Proof.
  intros s s_opt [_ [Ht [Hm [Hg [He Hd]]]]].
  unfold with_funcs.
  rewrite Ht. rewrite Hm. rewrite Hg. rewrite He. rewrite Hd.
  destruct s_opt. reflexivity.
Qed.

Ltac wf_proj := cbn [s_funcs s_tables s_mems s_globals s_elems s_datas] in *.

Ltac with_funcs_solve :=
  cbv beta iota zeta delta
    [ with_funcs supdate_glob supdate_glob_s sglob_ind option_bind option_map
      stab_update stab_grow selem_drop sdata_drop smem_store
      smem_store_packed smem_store_vec smem_store_vec_lane smem_grow
      upd_s_mem ] in *;
  wf_proj;
  repeat (match goal with
          | H : None = Some _ |- _ => discriminate
          | H : Some _ = Some _ |- _ => injection H; intros; subst
          | H : (if ?b then _ else _) = Some _ |- _ => destruct b
          | H : (match ?x with _ => _ end) = Some _ |- _ => destruct x
          end; wf_proj);
  reflexivity.

Lemma supdate_glob_with_funcs : forall s fs inst i v s',
  supdate_glob s inst i v = Some s' ->
  supdate_glob (with_funcs s fs) inst i v = Some (with_funcs s' fs).
Proof. intros s fs inst i v s' H. with_funcs_solve. Qed.

Lemma stab_update_with_funcs : forall s fs inst x i tabv s',
  stab_update s inst x i tabv = Some s' ->
  stab_update (with_funcs s fs) inst x i tabv = Some (with_funcs s' fs).
Proof. intros s fs inst x i tabv s' H. with_funcs_solve. Qed.

Lemma selem_drop_with_funcs : forall s fs inst x s',
  selem_drop s inst x = Some s' ->
  selem_drop (with_funcs s fs) inst x = Some (with_funcs s' fs).
Proof. intros s fs inst x s' H. with_funcs_solve. Qed.

Lemma sdata_drop_with_funcs : forall s fs inst x s',
  sdata_drop s inst x = Some s' ->
  sdata_drop (with_funcs s fs) inst x = Some (with_funcs s' fs).
Proof. intros s fs inst x s' H. with_funcs_solve. Qed.

Lemma smem_store_with_funcs : forall s fs inst n off v t s',
  smem_store s inst n off v t = Some s' ->
  smem_store (with_funcs s fs) inst n off v t = Some (with_funcs s' fs).
Proof. intros s fs inst n off v t s' H. with_funcs_solve. Qed.

Lemma smem_store_packed_with_funcs : forall s fs inst n off v tp s',
  smem_store_packed s inst n off v tp = Some s' ->
  smem_store_packed (with_funcs s fs) inst n off v tp = Some (with_funcs s' fs).
Proof. intros s fs inst n off v tp s' H. with_funcs_solve. Qed.

Lemma smem_store_vec_with_funcs : forall s fs inst n v marg s',
  smem_store_vec s inst n v marg = Some s' ->
  smem_store_vec (with_funcs s fs) inst n v marg = Some (with_funcs s' fs).
Proof. intros s fs inst n v marg s' H. with_funcs_solve. Qed.

Lemma smem_store_vec_lane_with_funcs : forall s fs inst n v width marg x s',
  smem_store_vec_lane s inst n v width marg x = Some s' ->
  smem_store_vec_lane (with_funcs s fs) inst n v width marg x
    = Some (with_funcs s' fs).
Proof. intros s fs inst n v width marg x s' H. with_funcs_solve. Qed.

Lemma stab_grow_with_funcs : forall s fs inst x n init s' sz,
  stab_grow s inst x n init = Some (s', sz) ->
  stab_grow (with_funcs s fs) inst x n init = Some (with_funcs s' fs, sz).
Proof. intros s fs inst x n init s' sz H. with_funcs_solve. Qed.

Lemma smem_grow_with_funcs : forall s fs inst c s' sz,
  smem_grow s inst c = Some (s', sz) ->
  smem_grow (with_funcs s fs) inst c = Some (with_funcs s' fs, sz).
Proof. intros s fs inst c s' sz H. with_funcs_solve. Qed.

(* ── 2. What the host must promise ────────────────────────────────
   [host_application] takes the whole store and may return any store,
   so nothing below is derivable: it has to be assumed.  Each of these
   says the host cannot tell the two modules apart, which is exactly
   the condition under which renaming a callee's locals is invisible. *)

Definition host_transports : Prop :=
  forall hs s s_opt tf h vcs hs' s' r,
    store_rel s s_opt ->
    host_application hs s tf h vcs hs' (Some (s', r)) ->
    exists s_opt', host_application hs s_opt tf h vcs hs' (Some (s_opt', r))
                /\ store_rel s' s_opt'.

Definition host_transports_bwd : Prop :=
  forall hs s s_opt tf h vcs hs' s_opt' r,
    store_rel s s_opt ->
    host_application hs s_opt tf h vcs hs' (Some (s_opt', r)) ->
    exists s', host_application hs s tf h vcs hs' (Some (s', r))
            /\ store_rel s' s_opt'.

Definition host_transports_trap : Prop :=
  forall hs s s_opt tf h vcs hs',
    store_rel s s_opt ->
    (host_application hs s tf h vcs hs' None <->
     host_application hs s_opt tf h vcs hs' None).

Definition host_ok : Prop :=
  host_transports /\ host_transports_bwd /\ host_transports_trap.

(* ── 3. The simulation, against related stores ────────────────────
   This is [sim_step] with the shared store replaced by a related pair.
   Most cases are unchanged: the rules that read the store read only
   visibly-equal parts, and the rules that write it write those parts
   identically.  Two cases carry the content.

   [r_invoke_native] is the one the whole exercise is for.  The source
   invokes [code] and the optimized side invokes the [code_opt] that
   [funcinst_rel] hands back; the resulting [AI_frame]s are related by
   [rel_frame] at the callee's own map, whose two premises are exactly
   the two halves of [code_rel].  Note that [store_guarded] disappears:
   [sim_step] needed it only because it related the callee to *itself*
   under [empty], which required the callee's body to satisfy the
   nesting restriction.  Here the callee is related to its coalesced
   counterpart instead, and [rel_bs] already carries what is needed.

   [r_invoke_host_success] is where [host_transports] is used. *)

(* The successor stores.  Every rule but the host call leaves s_funcs
   alone, so the optimized successor is the source successor carrying
   the same optimized code. *)
Lemma store_rel_keep : forall s fs s',
  store_rel s (with_funcs s fs) -> s_funcs s' = s_funcs s ->
  store_rel s' (with_funcs s' fs).
Proof.
  intros s fs s' [Hf _] Heq. split.
  - cbn [s_funcs]. rewrite Heq. exact Hf.
  - repeat split; reflexivity.
Qed.

(* Ltac defined inside a Section does not survive it, so this is the
   same script as coalesce_locals_correct.v's store_funcs_solve. *)
Ltac keeps_funcs_solve :=
  cbv beta iota zeta delta
    [ supdate_glob supdate_glob_s sglob_ind option_bind option_map
      stab_update stab_grow selem_drop sdata_drop smem_store
      smem_store_packed smem_store_vec smem_store_vec_lane smem_grow
      upd_s_mem ] in *;
  repeat match goal with
         | H : None = Some _ |- _ => discriminate
         | H : Some _ = Some _ |- _ => injection H; intros; subst
         | H : (if ?b then _ else _) = Some _ |- _ => destruct b
         | H : (match ?x with _ => _ end) = Some _ |- _ => destruct x
         end;
  reflexivity.

Lemma supdate_glob_keeps_funcs : forall s inst i v s',
  supdate_glob s inst i v = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst i v s' H. keeps_funcs_solve. Qed.

Lemma stab_update_keeps_funcs : forall s inst x i tabv s',
  stab_update s inst x i tabv = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst x i tabv s' H. keeps_funcs_solve. Qed.

Lemma selem_drop_keeps_funcs : forall s inst x s',
  selem_drop s inst x = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst x s' H. keeps_funcs_solve. Qed.

Lemma sdata_drop_keeps_funcs : forall s inst x s',
  sdata_drop s inst x = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst x s' H. keeps_funcs_solve. Qed.

Lemma smem_store_keeps_funcs : forall s inst n off v t s',
  smem_store s inst n off v t = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst n off v t s' H. keeps_funcs_solve. Qed.

Lemma smem_store_packed_keeps_funcs : forall s inst n off v tp s',
  smem_store_packed s inst n off v tp = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst n off v tp s' H. keeps_funcs_solve. Qed.

Lemma smem_store_vec_keeps_funcs : forall s inst n v marg s',
  smem_store_vec s inst n v marg = Some s' -> s_funcs s' = s_funcs s.
Proof. intros s inst n v marg s' H. keeps_funcs_solve. Qed.

Lemma smem_store_vec_lane_keeps_funcs : forall s inst n v width marg x s',
  smem_store_vec_lane s inst n v width marg x = Some s' ->
  s_funcs s' = s_funcs s.
Proof. intros s inst n v width marg x s' H. keeps_funcs_solve. Qed.

Lemma stab_grow_keeps_funcs : forall s inst x n init s' sz,
  stab_grow s inst x n init = Some (s', sz) -> s_funcs s' = s_funcs s.
Proof. intros s inst x n init s' sz H. keeps_funcs_solve. Qed.

Lemma smem_grow_keeps_funcs : forall s inst c s' sz,
  smem_grow s inst c = Some (s', sz) -> s_funcs s' = s_funcs s.
Proof. intros s inst c s' sz H. keeps_funcs_solve. Qed.

(* The three tactic families the induction needs.  They are [sim_plain]
   and friends from coalesce_locals_correct.v with the extra store
   witness threaded through. *)

(* A store operation that fails does *not* transfer by conversion: in
   the None case the new record sits in the dead branch, and there the
   two sides really do differ -- one carries fs, the other s_funcs s.
   The two propositions are still equivalent, since whether the match is
   None does not depend on what the dead branch builds.  These are the
   seven operations that both build a store and have a failure rule. *)
Ltac none_wf_solve :=
  cbv beta iota zeta delta
    [ with_funcs supdate_glob supdate_glob_s sglob_ind option_bind option_map
      stab_update stab_grow smem_store smem_store_packed smem_store_vec
      smem_store_vec_lane smem_grow upd_s_mem ] in *;
  wf_proj;
  repeat (match goal with
          | H : Some _ = None |- _ => discriminate
          | H : (if ?b then _ else _) = None |- _ => destruct b
          | H : (match ?x with _ => _ end) = None |- _ => destruct x
          end; wf_proj);
  reflexivity.

Lemma stab_update_none_wf : forall s fs inst x i tabv,
  stab_update s inst x i tabv = None ->
  stab_update (with_funcs s fs) inst x i tabv = None.
Proof. intros s fs inst x i tabv H. none_wf_solve. Qed.

Lemma stab_grow_none_wf : forall s fs inst x n init,
  stab_grow s inst x n init = None ->
  stab_grow (with_funcs s fs) inst x n init = None.
Proof. intros s fs inst x n init H. none_wf_solve. Qed.

Lemma smem_store_none_wf : forall s fs inst n off v t,
  smem_store s inst n off v t = None ->
  smem_store (with_funcs s fs) inst n off v t = None.
Proof. intros s fs inst n off v t H. none_wf_solve. Qed.

Lemma smem_store_packed_none_wf : forall s fs inst n off v tp,
  smem_store_packed s inst n off v tp = None ->
  smem_store_packed (with_funcs s fs) inst n off v tp = None.
Proof. intros s fs inst n off v tp H. none_wf_solve. Qed.

Lemma smem_store_vec_none_wf : forall s fs inst n v marg,
  smem_store_vec s inst n v marg = None ->
  smem_store_vec (with_funcs s fs) inst n v marg = None.
Proof. intros s fs inst n v marg H. none_wf_solve. Qed.

Lemma smem_store_vec_lane_none_wf : forall s fs inst n v width marg x,
  smem_store_vec_lane s inst n v width marg x = None ->
  smem_store_vec_lane (with_funcs s fs) inst n v width marg x = None.
Proof. intros s fs inst n v width marg x H. none_wf_solve. Qed.

Lemma smem_grow_none_wf : forall s fs inst c,
  smem_grow s inst c = None ->
  smem_grow (with_funcs s fs) inst c = None.
Proof. intros s fs inst c H. none_wf_solve. Qed.

Ltac wf_none :=
  first [ apply stab_update_none_wf; eassumption
        | apply stab_grow_none_wf; eassumption
        | apply smem_store_none_wf; eassumption
        | apply smem_store_packed_none_wf; eassumption
        | apply smem_store_vec_none_wf; eassumption
        | apply smem_store_vec_lane_none_wf; eassumption
        | apply smem_grow_none_wf; eassumption ].

Ltac sim_plain_store :=
  match goal with
  | Hrel : rel_es _ _ _ ?eo |- _ =>
      apply rel_es_plain_inv in Hrel; [ subst eo | solve [plain_solve] ]
  end;
  match goal with
  | Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 3 eexists; split; [| split; [| split]];
      [ econstructor; rewrite <- ? Hinst;
        first [ eassumption | reflexivity | wf_none ]
      | eassumption
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

(* econstructor commits to the first constructor whose conclusion
   unifies, and with the successor list still an evar the *_success rule
   always unifies before its *_failure sibling.  So the failure rules
   have to be named. *)
Ltac sim_plain_rule R :=
  match goal with
  | Hrel : rel_es _ _ _ ?eo |- _ =>
      apply rel_es_plain_inv in Hrel; [ subst eo | solve [plain_solve] ]
  end;
  match goal with
  | Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 3 eexists; split; [| split; [| split]];
      [ eapply R; rewrite <- ? Hinst;
        first [ eassumption | reflexivity | wf_none ]
      | eassumption
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

Ltac sim_get_store :=
  match goal with
  | Hst : store_rel ?s (with_funcs ?s ?fs) |- _ =>
      exists (with_funcs s fs);
      let Hr := fresh in let Hr1 := fresh in let Hr2 := fresh in
      edestruct (sim_local_get _ _ _ _ _ (with_funcs s fs))
        as [? [? [Hr [Hr1 Hr2]]]];
        [ eassumption | eassumption | eassumption |];
      do 2 eexists;
      split; [exact Hr | split; [exact Hst | split; [exact Hr1 | exact Hr2]]]
  end.

Ltac sim_set_store :=
  match goal with
  | Hst : store_rel ?s (with_funcs ?s ?fs) |- _ =>
      exists (with_funcs s fs);
      let Hr := fresh in let Hr1 := fresh in let Hr2 := fresh in
      edestruct (sim_local_set _ _ _ _ _ _ (with_funcs s fs))
        as [? [? [Hr [Hr1 Hr2]]]];
        [ eassumption | apply leq_to_lt; eassumption | eassumption
        | eassumption | eassumption |];
      do 2 eexists;
      split; [exact Hr | split; [exact Hst | split; [exact Hr1 | exact Hr2]]]
  end.

(* A rule that writes the store: the optimized side runs the same
   operation on the same visible sections, and the successor stores are
   related because the operation leaves s_funcs alone. *)
Ltac sim_storeop R Lwf Lkf :=
  match goal with
  | Hrel : rel_es _ _ _ ?eo |- _ =>
      apply rel_es_plain_inv in Hrel; [ subst eo | solve [plain_solve] ]
  end;
  match goal with
  | Hst : store_rel ?s (with_funcs ?s ?fs), Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 3 eexists; split; [| split; [| split]];
      [ eapply R; rewrite <- ? Hinst;
        first [ apply Lwf; eassumption | eassumption | reflexivity ]
      | eapply store_rel_keep; [ exact Hst | eapply Lkf; eassumption ]
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

(* [return_call_indirect] is proved from a nested call_indirect step, so
   that step has to be replayed on the optimized store as well.  Unlike
   the plain call, call_indirect reads s_funcs -- for the type check --
   so the replay needs the store relation.  These are
   coalesce_locals_correct.v's transports with that one side condition
   routed through funcinst_rel. *)
Lemma reduce_call_indirect_success_wf :
  forall hs s fs f v x y a f_src,
    store_rel s (with_funcs s fs) ->
    reduce hs s f [v_to_e v; AI_basic (BI_call_indirect x y)] hs s f [AI_invoke a] ->
    f_inst f_src = f_inst f ->
    reduce hs (with_funcs s fs) f_src
             [v_to_e v; AI_basic (BI_call_indirect x y)]
           hs (with_funcs s fs) f_src [AI_invoke a].
Proof.
  intros hs s fs f v x y a f_src Hst Hred.
  revert f_src.
  remember [v_to_e v; AI_basic (BI_call_indirect x y)] as e eqn:He.
  remember [AI_invoke a] as e' eqn:He'.
  revert Hst.
  induction Hred; intros Hst f_src Hinst; try (inversion He); try (discriminate He').
  - apply r_simple. rewrite He in H. exact H.
  - subst x0 y0.
    destruct (store_rel_lookup _ _ _ _ Hst H0) as [cl_o [Hlk Hfi]].
    eapply r_call_indirect_success;
      [ rewrite <- Hinst in H; exact H
      | exact Hlk
      | rewrite <- Hinst in H1; rewrite (funcinst_rel_type _ _ Hfi); exact H1 ].
  - assert (Hin : In (AI_invoke a0) [v_to_e v; AI_basic (BI_call_indirect x y)]).
    { rewrite <- He. apply in_or_app. right. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [Hv | Hinv].
    + destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
      destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
    + destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs].
  - rewrite He in H. rewrite He' in H0.
    assert (Hfill : es = [v_to_e v; AI_basic (BI_call_indirect x y)]
                    /\ es' = [AI_invoke a]).
    { eapply lfill_singleton_invert; [exact H | exact H0 | | ].
      { intro Hm. destruct v as [vn | vv | r]; compute in Hm; try discriminate Hm.
        destruct r as [t | fa | ea]; compute in Hm; discriminate Hm. }
      { intro Hc. cbv in Hc. discriminate Hc. } }
    destruct Hfill as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hst | exact Hinst].
Qed.

Lemma reduce_call_indirect_failure_wf :
  forall hs s fs f v x y f_src,
    store_rel s (with_funcs s fs) ->
    reduce hs s f [v_to_e v; AI_basic (BI_call_indirect x y)] hs s f [AI_trap] ->
    f_inst f_src = f_inst f ->
    reduce hs (with_funcs s fs) f_src
             [v_to_e v; AI_basic (BI_call_indirect x y)]
           hs (with_funcs s fs) f_src [AI_trap].
Proof.
  intros hs s fs f v x y f_src Hst Hred.
  revert f_src.
  remember [v_to_e v; AI_basic (BI_call_indirect x y)] as e eqn:He.
  remember [AI_trap] as e' eqn:He'.
  revert Hst.
  induction Hred; intros Hst f_src Hinst; try (inversion He); try (discriminate He').
  - apply r_simple. rewrite He in H. exact H.
  - subst x0 y0.
    destruct (store_rel_lookup _ _ _ _ Hst H0) as [cl_o [Hlk Hfi]].
    eapply r_call_indirect_failure_mismatch;
      [ rewrite <- Hinst in H; exact H
      | exact Hlk
      | rewrite <- Hinst in H1; rewrite (funcinst_rel_type _ _ Hfi); exact H1 ].
  - subst x0 y0. eapply r_call_indirect_failure_bound;
      rewrite <- Hinst in H; exact H.
  - subst x0 y0. eapply r_call_indirect_failure_null_ref;
      rewrite <- Hinst in H; exact H.
  - assert (Hin : In (AI_invoke a) [v_to_e v; AI_basic (BI_call_indirect x y)]).
    { rewrite <- He. apply in_or_app. right. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [Hv | Hinv].
    + destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
      destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
    + destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs].
  - assert (Hin : In (AI_invoke a) [v_to_e v; AI_basic (BI_call_indirect x y)]).
    { rewrite <- He. apply in_or_app. right. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [Hv | Hinv].
    + destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
      destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
    + destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs].
  - rewrite He in H. rewrite He' in H0.
    assert (Hfill : es = [v_to_e v; AI_basic (BI_call_indirect x y)]
                    /\ es' = [AI_trap]).
    { eapply lfill_singleton_invert; [exact H | exact H0 | | ].
      { intro Hm. destruct v as [vn | vv | r]; compute in Hm; try discriminate Hm.
        destruct r as [t | fa | ea]; compute in Hm; discriminate Hm. }
      { intro Hc. cbv in Hc. discriminate Hc. } }
    destruct Hfill as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hst | exact Hinst].
Qed.

Lemma sim_step_store_wf : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  host_ok ->
  forall fs phi K f_o es_o,
    store_rel s (with_funcs s fs) ->
    rel_es phi K es es_o ->
    frames_agree phi (live_ext es K) f f_o ->
    exists s_opt' f_o' es_o',
      reduce hs (with_funcs s fs) f_o es_o hs' s_opt' f_o' es_o' /\
      store_rel s' s_opt' /\
      rel_es phi K es' es_o' /\
      frames_agree phi (live_ext es' K) f' f_o'.
Proof.
  intros hs s f es hs' s' f' es' Hred Hhost.
  induction Hred; intros fs phi K f_o es_o Hst Hrel Hfr.
  all: try (solve [ sim_plain_store ]).
  all: try (solve [ sim_get_store ]).
  all: try (solve [ sim_set_store ]).
  all: try (solve [ sim_plain_rule r_table_get_failure ]).
  all: try (solve [ sim_plain_rule r_table_set_failure ]).
  all: try (solve [ sim_plain_rule r_table_grow_failure ]).
  all: try (solve [ sim_plain_rule r_load_failure ]).
  all: try (solve [ sim_plain_rule r_load_packed_failure ]).
  all: try (solve [ sim_plain_rule r_load_vec_failure ]).
  all: try (solve [ sim_plain_rule r_load_vec_lane_failure ]).
  all: try (solve [ sim_plain_rule r_store_failure ]).
  all: try (solve [ sim_plain_rule r_store_packed_failure ]).
  all: try (solve [ sim_plain_rule r_store_vec_failure ]).
  all: try (solve [ sim_plain_rule r_store_vec_lane_failure ]).
  all: try (solve [ sim_plain_rule r_memory_grow_failure ]).
  all: try (solve [ sim_storeop r_global_set supdate_glob_with_funcs
                                supdate_glob_keeps_funcs ]).
  all: try (solve [ sim_storeop r_table_set_success stab_update_with_funcs
                                stab_update_keeps_funcs ]).
  all: try (solve [ sim_storeop r_table_grow_success stab_grow_with_funcs
                                stab_grow_keeps_funcs ]).
  all: try (solve [ sim_storeop r_elem_drop selem_drop_with_funcs
                                selem_drop_keeps_funcs ]).
  all: try (solve [ sim_storeop r_data_drop sdata_drop_with_funcs
                                sdata_drop_keeps_funcs ]).
  all: try (solve [ sim_storeop r_store_success smem_store_with_funcs
                                smem_store_keeps_funcs ]).
  all: try (solve [ sim_storeop r_store_packed_success smem_store_packed_with_funcs
                                smem_store_packed_keeps_funcs ]).
  all: try (solve [ sim_storeop r_store_vec_success smem_store_vec_with_funcs
                                smem_store_vec_keeps_funcs ]).
  all: try (solve [ sim_storeop r_store_vec_lane_success smem_store_vec_lane_with_funcs
                                smem_store_vec_lane_keeps_funcs ]).
  all: try (solve [ sim_storeop r_memory_grow_success smem_grow_with_funcs
                                smem_grow_keeps_funcs ]).
  { (* r_simple *)
    destruct (sim_simple _ _ H phi K es_o Hrel) as [es_o' [Hrs [Hrel' Hsub]]].
    exists (with_funcs s fs), f_o, es_o'. split; [| split; [| split]].
    - apply r_simple. exact Hrs.
    - exact Hst.
    - exact Hrel'.
    - exact (frames_agree_sub _ _ _ _ _ Hsub Hfr).
  }
  { (* r_block *)
    apply rel_es_split in Hrel.
    destruct Hrel as [X1 [X2 [HeqX [Hr1 Hr2]]]].
    apply rel_es_plain_inv in Hr1; [| apply es_plain_const_list; assumption ].
    subst X1.
    apply rel_es_cons_inv in Hr2. destruct Hr2 as [e_o [t_o [Heq2 [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst X2. subst es_o.
    apply rel_e_basic_inv in He. destruct He as [b_o [Hbo Hb]]. subst e_o.
    apply rel_b_block_inv in Hb. destruct Hb as [bs_o [Hbo2 [Hbw Hbs]]].
    subst b_o.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_block; [ rewrite <- Hinst; eassumption | eassumption
                      | eassumption | eassumption | eassumption ].
    - exact Hst.
    - apply rel_cons; [| apply rel_nil ].
      apply rel_label.
      + destruct Hbw as [Hbr | Hbw].
        * apply label_ok_nobr. rewrite es_br_cat.
          rewrite const_list_nobr; [| assumption ].
          rewrite bs_br_to_e_list. rewrite Hbr. reflexivity.
        * apply label_ok_nohazard. rewrite es_hazard_app.
          rewrite es_hazard_const; [| assumption ].
          rewrite es_hazard_to_e_list. rewrite Hbw. reflexivity.
      + apply rel_nil.
      + apply rel_es_app.
        * apply rel_es_plain. apply es_plain_const_list. assumption.
        * eapply rel_es_weaken; [ apply rel_es_to_e_list; exact Hbs |].
          intros i [Habs | Hk]; [ discriminate Habs | exact Hk ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl.
      rewrite live_ext_label_nil in Hl.
      rewrite live_ext_const_app in Hl; [| assumption ].
      rewrite live_ext_to_e_list in Hl.
      rewrite live_ext_const_app; [| assumption ].
      rewrite live_ext_block.
      unfold bs_live_ext in Hl.
      destruct Hl as [H' | [_ H']]; [ left; exact H' | right; exact H' ].
  }
  { (* r_loop *)
    apply rel_es_split in Hrel.
    destruct Hrel as [X1 [X2 [HeqX [Hr1 Hr2]]]].
    apply rel_es_plain_inv in Hr1; [| apply es_plain_const_list; assumption ].
    subst X1.
    apply rel_es_cons_inv in Hr2. destruct Hr2 as [e_o [t_o [Heq2 [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst X2. subst es_o.
    apply rel_e_basic_inv in He. destruct He as [b_o [Hbo Hb]]. subst e_o.
    apply rel_b_loop_inv in Hb. destruct Hb as [bs_o [Hbo2 [Hnw Hbs]]]. subst b_o.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_loop; [ rewrite <- Hinst; eassumption | eassumption
                     | eassumption | eassumption | eassumption ].
    - exact Hst.
    - apply rel_cons; [| apply rel_nil ].
      apply rel_label.
      + destruct Hnw as [Hbr | Hnw'].
        * apply label_ok_nobr. rewrite es_br_cat.
          rewrite const_list_nobr; [| assumption ].
          rewrite bs_br_to_e_list. rewrite Hbr. reflexivity.
        * apply label_ok_nohazard. rewrite es_hazard_app.
          rewrite es_hazard_const; [| assumption ].
          rewrite es_hazard_to_e_list. rewrite Hnw'. reflexivity.
      + apply rel_cons; [| apply rel_nil ].
        apply rel_basic. apply relb_loop; [ exact Hnw |].
        eapply rel_bs_weaken; [ exact Hbs |].
        intros i [Hl | Hl]; [ left; exact Hl |].
        right. rewrite ! live_ext_nil in Hl. rewrite ! live_ext_nil. exact Hl.
      + apply rel_es_app.
        * apply rel_es_plain. apply es_plain_const_list. assumption.
        * eapply rel_es_weaken; [ apply rel_es_to_e_list; exact Hbs |].
          intros i [Hl | Hl]; [| right; exact Hl ].
          left. rewrite es_live_singleton in Hl. cbn [ai_live] in Hl.
          rewrite bi_live_loop in Hl. exact Hl.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl.
      rewrite live_ext_label in Hl.
      rewrite live_ext_const_app in Hl; [| assumption ].
      rewrite live_ext_to_e_list in Hl.
      rewrite live_ext_const_app; [| assumption ].
      rewrite live_ext_loop.
      unfold bs_live_ext in Hl.
      rewrite es_live_singleton in Hl. cbn [ai_live] in Hl.
      rewrite bi_live_loop in Hl.
      destruct Hl as [H' | [_ [H' | H']]];
        [ left; exact H' | left; exact H' | right; exact H' ].
  }
  { (* r_call_indirect_success: the type check reads s_funcs, and
       funcinst_rel keeps cl_type fixed *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup _ _ _ _ Hst H0) as [cl_o [Hlk Hfi]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_call_indirect_success.
      + rewrite <- Hinst. exact H.
      + exact Hlk.
      + rewrite <- Hinst. rewrite (funcinst_rel_type _ _ Hfi). exact H1.
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_call_indirect_failure_mismatch *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup _ _ _ _ Hst H0) as [cl_o [Hlk Hfi]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_call_indirect_failure_mismatch.
      + rewrite <- Hinst. exact H.
      + exact Hlk.
      + rewrite <- Hinst. rewrite (funcinst_rel_type _ _ Hfi). exact H1.
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - apply r_return_call. eapply reduce_call_transport;
        [ exact Hred | symmetry; exact Hinst ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call_indirect_success *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - apply r_return_call_indirect_success.
      eapply reduce_call_indirect_success_wf;
        [ exact Hst | exact Hred | symmetry; exact Hinst ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call_indirect_failure *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - apply r_return_call_indirect_failure.
      eapply reduce_call_indirect_failure_wf;
        [ exact Hst | exact Hred | symmetry; exact Hinst ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_invoke_native: the case the whole exercise is for.  The source
       enters [code]; the optimized side enters the [code_opt] that
       funcinst_rel hands back, and the two activations are related at
       the callee's own map by the two halves of code_rel.

       [code_opt] declares fewer locals, so its activation is built from
       its own, shorter, default vector -- which is why the entry half
       of code_rel hands back that vector rather than reusing the
       source's.  The label arity is [length ts2] and the argument
       count [length ts1], neither of which the pass touches, so the
       rest of the rule's premises are the hypotheses unchanged. *)
    subst ves. subst cl. subst code.
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup _ _ _ _ Hst H) as [cl_o [Hlk Hfi]].
    simpl in Hfi.
    destruct Hfi as [code_opt [Hcl_o [Hty [Hloc [psi [Hbs Hentry]]]]]].
    destruct code_opt as [xo tso eso]. cbn in Hty, Hloc, Hbs, Hentry.
    subst xo.
    destruct (defaults_of_not_none tso
                (fun Habs => ltac:(rewrite (proj2 Hloc Habs) in H7;
                                   discriminate H7)))
      as [defaults_o Hdo].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_invoke_native;
        [ rewrite Hcl_o in Hlk; exact Hlk | reflexivity | reflexivity
        | reflexivity | eassumption | reflexivity | eassumption
        | eassumption | exact Hdo ].
    - exact Hst.
    - apply rel_cons; [| apply rel_nil ].
      eapply rel_frame.
      + apply (Hentry inst vs defaults defaults_o _);
          [ congruence | exact H7 | exact Hdo ].
      + apply rel_cons; [| apply rel_nil ].
        apply rel_label; [| apply rel_nil |].
        * apply label_ok_dead; [ reflexivity |].
          intros i Hi. rewrite ! live_ext_nil in Hi. exact Hi.
        * eapply rel_es_weaken; [ apply rel_es_to_e_list; exact Hbs |].
          intros i [Habs | Habs];
            [ discriminate Habs | rewrite live_ext_nil in Habs; exact Habs ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl. rewrite live_ext_frame in Hl.
      apply live_ext_neutral_bwd; [ solve [neutral_solve] | exact Hl ].
  }
  { (* r_invoke_host_success: host_transports supplies the successor
       store, and with it the relation *)
    subst ves. subst cl.
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup _ _ _ _ Hst H) as [cl_o [Hlk Hfi]].
    simpl in Hfi. subst cl_o.
    destruct Hhost as [Htr [_ _]].
    destruct (Htr _ _ _ _ _ _ _ _ _ Hst H5) as [s_o' [Happ Hst']].
    exists s_o'. eexists. eexists. split; [| split; [| split]].
    - eapply r_invoke_host_success;
        [ exact Hlk | reflexivity | reflexivity | eassumption
        | eassumption | eassumption | exact Happ ].
    - exact Hst'.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_invoke_host_diverge *)
    subst ves. subst cl.
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup _ _ _ _ Hst H) as [cl_o [Hlk Hfi]].
    simpl in Hfi. subst cl_o.
    destruct Hhost as [_ [_ Htrap]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_invoke_host_diverge;
        [ exact Hlk | reflexivity | reflexivity | eassumption
        | eassumption | eassumption
        | exact (proj1 (Htrap _ _ _ _ _ _ _ Hst) H5) ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_invoke *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    subst es. apply rel_es_lfill_inv in Hes.
    destruct Hes as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv in Hhole; [| solve [plain_solve] ]. subst hole_o.
    subst esf_o.
    destruct (store_rel_lookup _ _ _ _ Hst H) as [cl_o [Hlk Hfi]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_return_invoke;
        [ exact Hlk | rewrite (funcinst_rel_type _ _ Hfi); exact H0
        | eassumption | eassumption | eassumption | eassumption
        | reflexivity ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl); solve [neutral_solve].
  }
  { (* r_local_get: neither side touches the store *)
    exists (with_funcs s fs).
    destruct (sim_local_get phi K f f_o hs (with_funcs s fs) j v es_o H Hrel Hfr)
      as [f_o' [es_o' [Hr [Hrel' Hfr']]]].
    exists f_o', es_o'.
    split; [exact Hr | split; [exact Hst | split; [exact Hrel' | exact Hfr']]].
  }
  { (* r_local_set *)
    exists (with_funcs s fs).
    destruct (sim_local_set phi K f f' f_o hs (with_funcs s fs) i v vd es_o
                H (leq_to_lt _ _ H0) H1 Hrel Hfr)
      as [f_o' [es_o' [Hr [Hrel' Hfr']]]].
    exists f_o', es_o'.
    split; [exact Hr | split; [exact Hst | split; [exact Hrel' | exact Hfr']]].
  }
  { (* r_label *)
    try subst les les'.
    apply rel_es_lfill_inv in Hrel.
    destruct Hrel as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]]. subst es_o.
    destruct (IHHred fs phi (lh_K lh K) f_o hole_o Hst Hhole
                (frames_agree_sub _ _ _ _ _
                   (fun i Hi => proj2 (live_ext_lfill _ lh es K i) Hi) Hfr))
      as [s_o' [f_o' [hole_o' [Hr [Hst' [Hrel' Hfr']]]]]].
    exists s_o', f_o', (lfill lh_o hole_o'). split; [| split; [| split]].
    - eapply r_label; [ exact Hr | reflexivity | reflexivity ].
    - exact Hst'.
    - apply rel_es_lfill; [ exact Hlh | | exact Hrel' ].
      eapply lh_labels_ok_step; [ exact Hred | exact Hok ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr').
      intros i Hi. apply live_ext_lfill. exact Hi.
  }
  { (* r_frame *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    assert (Hin : frames_agree psi (live_ext es (fun _ => False)) f fr_o).
    { refine (frames_agree_sub _ _ _ _ _ _ Hfa).
      intros ix Hi. unfold live_ext, es_live in *.
      destruct Hi as [H' | [_ Hf]]; [ exact H' | destruct Hf ]. }
    destruct (IHHred fs psi (fun _ => False) fr_o esf_o Hst Hes Hin)
      as [s_o' [fr_o' [esf_o' [Hr [Hst' [Hrel' Hfa']]]]]].
    exists s_o'. eexists. eexists. split; [| split; [| split]].
    - apply r_frame. exact Hr.
    - exact Hst'.
    - apply rel_cons; [| apply rel_nil ].
      eapply rel_frame; [| exact Hrel' ].
      refine (frames_agree_sub _ _ _ _ _ _ Hfa').
      intros i Hi. left. exact Hi.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl. apply live_ext_frame. apply live_ext_frame in Hl. exact Hl.
  }
Qed.

Theorem sim_step_store : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  host_ok ->
  forall s_opt phi K f_o es_o,
    store_rel s s_opt ->
    rel_es phi K es es_o ->
    frames_agree phi (live_ext es K) f f_o ->
    exists s_opt' f_o' es_o',
      reduce hs s_opt f_o es_o hs' s_opt' f_o' es_o' /\
      store_rel s' s_opt' /\
      rel_es phi K es' es_o' /\
      frames_agree phi (live_ext es' K) f' f_o'.
Proof.
  intros hs s f es hs' s' f' es' Hred Hhost s_opt phi K f_o es_o Hst Hrel Hfr.
  pose proof (store_rel_shape _ _ Hst) as Hshape.
  rewrite Hshape. rewrite Hshape in Hst.
  exact (sim_step_store_wf _ _ _ _ _ _ _ _ Hred Hhost _ phi K f_o es_o
           Hst Hrel Hfr).
Qed.

(* ── Inverting the relation from the optimized side ───────────────
   The backward simulation is driven by the *optimized* derivation, so
   every inversion coalesce_locals_correct.v does on the source shape is
   needed the other way round.  The relation is shape-preserving in both
   directions, so each of these is the same one-line inversion; only the
   local instructions differ, and there the source index is existential
   because phi merges. *)

(* The mirror inversions.  rel_e is shape-preserving in both directions:
   the only rel_b constructor whose output is a constant is relb_plain,
   whose input is the same constant. *)
Lemma rel_e_v_inv_r : forall phi K e v,
  rel_e phi K e (v_to_e v) -> e = v_to_e v.
Proof.
  intros phi K e v H.
  destruct v as [n | vv | vr]; simpl in H;
  [ | | destruct vr as [t | a | e']; simpl in H ];
  inversion H; subst; try reflexivity;
  match goal with
  | Hb : rel_b _ _ ?b ?bo |- _ => inversion Hb; subst; reflexivity
  end.
Qed.

Lemma rel_es_v_to_e_list_inv_r : forall phi K vs X,
  rel_es phi K X (v_to_e_list vs) -> X = v_to_e_list vs.
Proof.
  intros phi K vs. induction vs as [|v vs' IH]; intros X H; simpl in H.
  - inversion H; subst. reflexivity.
  - inversion H; subst. simpl. f_equal.
    + eapply rel_e_v_inv_r; eassumption.
    + apply IH. assumption.
Qed.

Lemma rel_es_cons_inv_r : forall phi K es e_o t_o,
  rel_es phi K es (e_o :: t_o) ->
  exists e t, es = e :: t /\ rel_e phi (live_ext t K) e e_o /\ rel_es phi K t t_o.
Proof.
  intros phi K es e_o t_o H. inversion H; subst.
  eexists; eexists; split; [reflexivity | split; eassumption].
Qed.

Lemma rel_e_basic_inv_r : forall phi K e b_o,
  rel_e phi K e (AI_basic b_o) ->
  exists b, e = AI_basic b /\ rel_b phi K b b_o.
Proof.
  intros phi K e b_o H. inversion H; subst.
  eexists; split; [reflexivity | eassumption].
Qed.

Lemma rel_b_get_inv_r : forall phi K b j,
  rel_b phi K b (BI_local_get j) ->
  exists i, b = BI_local_get i /\ apply_phi_local phi i = j.
Proof.
  intros phi K b j H. inversion H; subst.
  - cbn in H0. discriminate H0.
  - eexists; split; reflexivity.
Qed.

Lemma rel_b_set_inv_r : forall phi K b j,
  rel_b phi K b (BI_local_set j) ->
  exists i, b = BI_local_set i /\ apply_phi_local phi i = j /\ slot_free phi K i.
Proof.
  intros phi K b j H. inversion H; subst.
  - cbn in H0. discriminate H0.
  - eexists; split; [reflexivity | split; [reflexivity | assumption]].
Qed.

Lemma rel_b_tee_inv_r : forall phi K b j,
  rel_b phi K b (BI_local_tee j) ->
  exists i, b = BI_local_tee i /\ apply_phi_local phi i = j /\ slot_free phi K i.
Proof.
  intros phi K b j H. inversion H; subst.
  - cbn in H0. discriminate H0.
  - eexists; split; [reflexivity | split; [reflexivity | assumption]].
Qed.

Lemma rel_b_block_inv_r : forall phi K b bt bs_o,
  rel_b phi K b (BI_block bt bs_o) ->
  exists bs, b = BI_block bt bs /\ body_ok bs /\ rel_bs phi K bs bs_o.
Proof.
  intros phi K b bt bs_o H. inversion H; subst.
  - cbn in H0. discriminate H0.
  - eexists; split; [reflexivity | split; assumption].
Qed.

Lemma rel_b_loop_inv_r : forall phi K b bt bs_o,
  rel_b phi K b (BI_loop bt bs_o) ->
  exists bs, b = BI_loop bt bs /\ body_ok bs /\
    rel_bs phi (fun i => bs_live_b i bs = true \/ K i) bs bs_o.
Proof.
  intros phi K b bt bs_o H. inversion H; subst.
  - cbn in H0. discriminate H0.
  - eexists; split; [reflexivity | split; assumption].
Qed.

Lemma rel_b_if_inv_r : forall phi K b bt b1_o b2_o,
  rel_b phi K b (BI_if bt b1_o b2_o) ->
  exists bs1 bs2, b = BI_if bt bs1 bs2 /\ body_ok bs1 /\ body_ok bs2 /\
    rel_bs phi K bs1 b1_o /\ rel_bs phi K bs2 b2_o.
Proof.
  intros phi K b bt b1_o b2_o H. inversion H; subst.
  - cbn in H0. discriminate H0.
  - eexists; eexists; split;
    [reflexivity | split; [| split; [| split]]; assumption].
Qed.

Lemma rel_e_label_inv_r : forall phi K e n a_o b_o,
  rel_e phi K e (AI_label n a_o b_o) ->
  exists a b, e = AI_label n a b /\ label_ok a b K /\
    rel_es phi K a a_o /\
    rel_es phi (fun i => es_live_b i a = true \/ K i) b b_o.
Proof.
  intros phi K e n a_o b_o H. inversion H; subst.
  eexists; eexists; split;
    [reflexivity | split; [assumption | split; assumption]].
Qed.

Lemma rel_e_frame_inv_r : forall phi K e n fr_o es_o,
  rel_e phi K e (AI_frame n fr_o es_o) ->
  exists fr es psi, e = AI_frame n fr es /\
    frames_agree psi (es_live es) fr fr_o /\
    rel_es psi (fun _ => False) es es_o.
Proof.
  intros phi K e n fr_o es_o H. inversion H; subst.
  eexists; eexists; eexists; split; [reflexivity | split; eassumption].
Qed.

Lemma rel_e_plain_inv_r : forall phi K e e_o,
  rel_e phi K e e_o -> ai_plain e_o = true -> e = e_o.
Proof.
  intros phi K e e_o H Hp. destruct H; try reflexivity.
  - cbn in Hp. f_equal. destruct H; try reflexivity; cbn in Hp; discriminate Hp.
  - cbn in Hp. discriminate Hp.
  - cbn in Hp. discriminate Hp.
Qed.

Lemma rel_es_plain_inv_r : forall phi K es es_o,
  rel_es phi K es es_o -> es_plain es_o = true -> es = es_o.
Proof.
  intros phi K es es_o H. induction H as [| phi K e e_o es es_o He Hes IH];
  intros Hp; cbn in Hp; [reflexivity |].
  apply Bool.andb_true_iff in Hp. destruct Hp as [H1 H2].
  rewrite (IH H2). f_equal. eapply rel_e_plain_inv_r; eassumption.
Qed.

Lemma rel_es_split_r : forall phi K es1_o es2_o X,
  rel_es phi K X (es1_o ++ es2_o) ->
  exists X1 X2, X = X1 ++ X2 /\
    rel_es phi (live_ext X2 K) X1 es1_o /\
    rel_es phi K X2 es2_o.
Proof.
  intros phi K es1_o. induction es1_o as [| e_o es1' IH];
    intros es2_o X H; simpl in H.
  - exists nil, X. split; [reflexivity | split; [apply rel_nil | exact H]].
  - apply rel_es_cons_inv_r in H. destruct H as [e [t [Heq [He Ht]]]].
    subst X.
    destruct (IH es2_o t Ht) as [X1 [X2 [Heq1 [Hr1 Hr2]]]]. subst t.
    exists (e :: X1), X2. split; [reflexivity | split; [| exact Hr2]].
    apply rel_cons; [| exact Hr1].
    eapply rel_e_weaken; [ eassumption |].
    intros i Hi. apply live_ext_app. exact Hi.
Qed.

Lemma rel_es_lfill_inv_r : forall phi k (lh_o : lholed k) K es_o X,
  rel_es phi K X (lfill lh_o es_o) ->
  exists (lh : lholed k) es,
    X = lfill lh es /\
    rel_lh phi k K lh lh_o /\
    lh_labels_ok lh es K /\
    rel_es phi (lh_K lh K) es es_o.
Proof.
  intros phi k lh_o.
  induction lh_o as [ vs es'_o | k vs n es'_o lh_o IH es''_o ];
  intros K es_o X H; simpl in H.
  - apply rel_es_split_r in H. destruct H as [X0 [X1 [Heq [H0 H1]]]].
    apply rel_es_v_to_e_list_inv_r in H0. subst X0.
    apply rel_es_split_r in H1. destruct H1 as [Xh [Xt [Heq1 [Hh Ht]]]].
    exists (LH_base vs Xt), Xh. split; [| split; [| split]].
    + simpl. rewrite Heq. rewrite Heq1. reflexivity.
    + apply rel_lh_base. exact Ht.
    + exact I.
    + exact Hh.
  - apply rel_es_split_r in H. destruct H as [X0 [X1 [Heq [H0 H1]]]].
    apply rel_es_v_to_e_list_inv_r in H0. subst X0.
    change (rel_es phi K X1
              (AI_label n es'_o (lfill lh_o es_o) :: es''_o)) in H1.
    apply rel_es_cons_inv_r in H1.
    destruct H1 as [e [t [Heqe [Hlab Htail]]]]. subst X1.
    apply rel_e_label_inv_r in Hlab.
    destruct Hlab as [a [b [Heqa [Hlab' [Ha Hb]]]]]. subst e.
    destruct (IH (fun i => es_live_b i a = true \/ live_ext t K i) es_o b Hb)
      as [lh [hole [Heqb [Hlh [Hok Hhole]]]]].
    exists (LH_rec vs n a lh t), hole. split; [| split; [| split]].
    + simpl. rewrite Heq. rewrite Heqb. reflexivity.
    + apply rel_lh_rec; [ exact Ha | exact Hlh | exact Htail ].
    + simpl. split; [ rewrite <- Heqb; exact Hlab' | exact Hok ].
    + exact Hhole.
Qed.

(* rs_trap needs the trap-context inversion the other way round too. *)
Lemma rel_lh_trap_inv_r : forall phi k K (lh lh_o : lholed k),
  rel_lh phi k K lh lh_o ->
  lfill lh [AI_trap] = [AI_trap] -> lfill lh_o [AI_trap] = [AI_trap].
Proof.
  intros phi k K lh lh_o H.
  induction H; intros Habs; simpl in *.
  - destruct vs as [|v0 vs0]; simpl in *.
    + destruct es' as [|z zs]; simpl in Habs.
      * match goal with
        | Hx : rel_es _ _ nil _ |- _ => rewrite (rel_es_nil_inv _ _ _ Hx)
        end. reflexivity.
      * exfalso. injection Habs as Hz. discriminate Hz.
    + exfalso. destruct v0 as [ | | r0]; simpl in Habs; try discriminate Habs.
      destruct r0; simpl in Habs; discriminate Habs.
  - destruct vs as [|v0 vs0]; simpl in Habs.
    + discriminate Habs.
    + exfalso. destruct v0 as [ | | r0]; simpl in Habs; try discriminate Habs.
      destruct r0; simpl in Habs; discriminate Habs.
Qed.

(* The mirror of sim_simple.  reduce_simple never touches the locals, so
   only the live-set containment has to come back out -- and that is a
   statement about the source side alone, so every third bullet here is
   its forward twin verbatim.  What changes is the inversions, which all
   run from the optimized shape. *)
Ltac sim_simple_plain_bwd :=
  match goal with
  | Hrel : rel_es _ _ ?e _ |- _ =>
      apply rel_es_plain_inv_r in Hrel; [ subst e | solve [plain_solve] ]
  end;
  eexists; split; [| split];
  [ econstructor; first [ eassumption | reflexivity ]
  | apply rel_es_plain; solve [plain_solve]
  | live_sub_solve ].

Lemma sim_simple_bwd : forall es_o es_o',
  reduce_simple es_o es_o' ->
  forall phi K X,
    rel_es phi K X es_o ->
    exists X',
      reduce_simple X X' /\
      rel_es phi K X' es_o' /\
      (forall i, live_ext X' K i -> live_ext X K i).
Proof.
  intros es_o es_o' Hrs. induction Hrs; intros phi K X Hrel.
  all: try (solve [ sim_simple_plain_bwd ]).
  { (* rs_label_const *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t. subst X.
    apply rel_e_label_inv_r in He.
    destruct He as [a [b [Hlo [Hlab [Ha Hb]]]]]. subst e.
    apply rel_es_plain_inv_r in Hb; [| apply es_plain_const_list; assumption ].
    subst b.
    eexists. split; [| split].
    - apply rs_label_const. assumption.
    - apply rel_es_plain. apply es_plain_const_list. assumption.
    - intros ix Hl. rewrite live_ext_label.
      refine (live_ext_neutral_bwd _ _ ix _ _);
        [ apply es_neutral_const_list; assumption |].
      right. refine (live_ext_neutral_fwd _ _ ix _ Hl).
      apply es_neutral_const_list; assumption.
  }
  { (* rs_label_trap *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t. subst X.
    apply rel_e_label_inv_r in He.
    destruct He as [a [b [Hlo [Hlab [Ha Hb]]]]]. subst e.
    apply rel_es_plain_inv_r in Hb; [| solve [plain_solve] ]. subst b.
    eexists. split; [| split].
    - apply rs_label_trap.
    - apply rel_es_plain. solve [plain_solve].
    - intros ix Hl. destruct (live_ext_trap K ix Hl).
  }
  { (* rs_if_false *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply (rel_e_v_inv_r _ _ _ (VAL_num (VAL_int32 c))) in He. subst e.
    apply rel_es_cons_inv_r in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
    apply rel_es_nil_inv_r in Ht1. subst t1. subst t. subst X.
    apply rel_e_basic_inv_r in He1. destruct He1 as [b [Hb1 Hb]]. subst e1.
    apply rel_b_if_inv_r in Hb.
    destruct Hb as [bs1 [bs2 [Hbo [Hw1 [Hw2 [Hr1 Hr2]]]]]]. subst b.
    eexists. split; [| split].
    - apply rs_if_false. assumption.
    - apply rel_cons; [| apply rel_nil ].
      apply rel_basic. apply relb_block; [ exact Hw2 | exact Hr2 ].
    - intros ix Hl. rewrite live_ext_block in Hl.
      rewrite live_ext_neutral_cons; [| reflexivity ].
      rewrite live_ext_if.
      destruct Hl as [H' | H']; [| right; exact H' ].
      left. rewrite H'. apply Bool.orb_true_r.
  }
  { (* rs_if_true *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply (rel_e_v_inv_r _ _ _ (VAL_num (VAL_int32 c))) in He. subst e.
    apply rel_es_cons_inv_r in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
    apply rel_es_nil_inv_r in Ht1. subst t1. subst t. subst X.
    apply rel_e_basic_inv_r in He1. destruct He1 as [b [Hb1 Hb]]. subst e1.
    apply rel_b_if_inv_r in Hb.
    destruct Hb as [bs1 [bs2 [Hbo [Hw1 [Hw2 [Hr1 Hr2]]]]]]. subst b.
    eexists. split; [| split].
    - apply rs_if_true. assumption.
    - apply rel_cons; [| apply rel_nil ].
      apply rel_basic. apply relb_block; [ exact Hw1 | exact Hr1 ].
    - intros ix Hl. rewrite live_ext_block in Hl.
      rewrite live_ext_neutral_cons; [| reflexivity ].
      rewrite live_ext_if.
      destruct Hl as [H' | H']; [| right; exact H' ].
      left. rewrite H'. reflexivity.
  }
  { (* rs_br *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t. subst X.
    apply rel_e_label_inv_r in He.
    destruct He as [a [b [Hlo [Hlab [Ha Hb]]]]]. subst e.
    subst LI. apply rel_es_lfill_inv_r in Hb.
    destruct Hb as [lh_s [hole_s [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv_r in Hhole; [| solve [plain_solve] ]. subst hole_s.
    subst b.
    eexists. split; [| split].
    - eapply rs_br; [ eassumption | eassumption | reflexivity ].
    - apply rel_es_app.
      + apply rel_es_plain. apply es_plain_const_list. assumption.
      + eapply rel_es_weaken; [ exact Ha |].
        intros ix Hx. apply live_ext_nil. exact Hx.
    - intros ix Hl.
      rewrite live_ext_const_app in Hl; [| assumption ].
      rewrite live_ext_label.
      destruct Hlab as [Hbr | [Hhaz | [[Hla Hnk] | Htr]]].
      + exfalso. eapply es_br_no_br. eassumption.
      + unfold live_ext in Hl |- *.
        right. split; [ exact (es_hazard_kills ix _ Hhaz) |].
        destruct Hl as [H' | [_ H']]; [ left; exact H' | right; exact H' ].
      + exfalso. unfold live_ext in Hl.
        destruct Hl as [H' | [_ H']].
        * rewrite (Hla ix) in H'. discriminate H'.
        * apply (Hnk ix). apply live_ext_nil. exact H'.
      + exfalso. eapply trapping_no_br; [ eassumption | exact Htr ].
  }
  { (* rs_local_const *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t. subst X.
    apply rel_e_frame_inv_r in He.
    destruct He as [fr [esf [psi [Hfo [Hfa Hes]]]]]. subst e.
    apply rel_es_plain_inv_r in Hes; [| apply es_plain_const_list; assumption ].
    subst esf.
    eexists. split; [| split].
    - eapply rs_local_const; eassumption.
    - apply rel_es_plain. apply es_plain_const_list. assumption.
    - intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl).
      apply es_neutral_const_list; assumption.
  }
  { (* rs_local_trap *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t. subst X.
    apply rel_e_frame_inv_r in He.
    destruct He as [fr [esf [psi [Hfo [Hfa Hes]]]]]. subst e.
    apply rel_es_plain_inv_r in Hes; [| solve [plain_solve] ]. subst esf.
    eexists. split; [| split].
    - apply rs_local_trap.
    - apply rel_es_plain. solve [plain_solve].
    - intros ix Hl. destruct (live_ext_trap K ix Hl).
  }
  { (* rs_local_tee *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_e_v_inv_r in He. subst e.
    apply rel_es_cons_inv_r in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
    apply rel_es_nil_inv_r in Ht1. subst t1. subst t. subst X.
    apply rel_e_basic_inv_r in He1. destruct He1 as [b [Hb1 Hb]]. subst e1.
    apply rel_b_tee_inv_r in Hb. destruct Hb as [i0 [Hbo [Hji Hsf]]]. subst b.
    eexists. split; [| split].
    - apply rs_local_tee.
    - rewrite <- Hji.
      apply rel_cons; [ apply rel_e_v_to_e |].
      apply rel_cons; [ apply rel_e_v_to_e |].
      apply rel_cons; [| apply rel_nil ].
      apply rel_basic. apply relb_set. exact Hsf.
    - intros ix Hl. unfold live_ext in *.
      cbn [es_live_b es_kills_b ai_live ai_kills bi_live bi_kills] in Hl |- *.
      destruct (live_v_to_e ix v) as [Hlv Hkv].
      rewrite Hlv in Hl. rewrite Hkv in Hl. rewrite Hlv. rewrite Hkv.
      simpl in Hl |- *. exact Hl.
  }
  { (* rs_return *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t. subst X.
    apply rel_e_frame_inv_r in He.
    destruct He as [fr [esf [psi [Hfo [Hfa Hes]]]]]. subst e.
    subst es. apply rel_es_lfill_inv_r in Hes.
    destruct Hes as [lh_s [hole_s [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv_r in Hhole; [| solve [plain_solve] ]. subst hole_s.
    subst esf.
    eexists. split; [| split].
    - eapply rs_return; [ eassumption | eassumption | reflexivity ].
    - apply rel_es_plain. apply es_plain_const_list. assumption.
    - intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl).
      apply es_neutral_const_list; assumption.
  }
  { (* rs_trap *)
    subst es. apply rel_es_lfill_inv_r in Hrel.
    destruct Hrel as [lh_s [hole_s [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv_r in Hhole; [| solve [plain_solve] ]. subst hole_s.
    subst X.
    eexists. split; [| split].
    - eapply rs_trap; [| reflexivity ].
      intros Habs. apply H. eapply rel_lh_trap_inv_r; eassumption.
    - apply rel_es_plain. solve [plain_solve].
    - intros ix Hl. destruct (live_ext_trap K ix Hl).
  }
Qed.

(* ── The two backward local cases ─────────────────────────────────
   Mirrors of [sim_local_get] and [sim_local_set].  The frame agreement
   runs the same way, but which index is known to be in range has
   swapped: the optimized side takes the step, so the slot is the given
   one and the source index -- which the relation pins down only up to
   [apply_phi_local phi i = j] -- has to be brought into range by the
   converse in-range component of [frames_agree].  That component exists
   for exactly this purpose. *)
Lemma sim_local_get_bwd : forall phi K f f_o hs s j v es,
  lookup_N (f_locs f_o) j = Some v ->
  rel_es phi K es [AI_basic (BI_local_get j)] ->
  frames_agree phi (live_ext es K) f f_o ->
  exists f' es',
    reduce hs s f es hs s f' es' /\
    rel_es phi K es' [v_to_e v] /\
    frames_agree phi (live_ext es' K) f' f_o.
Proof.
  intros phi K f f_o hs s j v es H Hrel Hfr.
  apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
  apply rel_es_nil_inv_r in Ht. subst t. subst es.
  apply rel_e_basic_inv_r in He. destruct He as [b [Heb Hb]]. subst e.
  apply rel_b_get_inv_r in Hb. destruct Hb as [i [Hbi Hji]]. subst b. subst j.
  destruct Hfr as [Hinst [Hlen [Hlenb HR]]].
  unfold lookup_N in H.
  assert (Hj : N.to_nat (apply_phi_local phi i) < length (f_locs f_o)).
  { apply (proj1 (nth_error_Some (f_locs f_o)
                    (N.to_nat (apply_phi_local phi i)))).
    intro Hnone. rewrite H in Hnone. discriminate Hnone. }
  assert (Hi : N.to_nat i < length (f_locs f)) by (apply Hlenb; exact Hj).
  assert (Hnth : nth_error (f_locs f) (N.to_nat i)
                 = nth_error (f_locs f_o) (N.to_nat (apply_phi_local phi i))).
  { apply HR; [ exact Hi |]. left. simpl. rewrite N.eqb_refl. reflexivity. }
  exists f, [v_to_e v]. split; [| split].
  - apply r_local_get. unfold lookup_N. rewrite Hnth. exact H.
  - apply rel_cons; [ apply rel_e_v_to_e | apply rel_nil ].
  - split; [ exact Hinst | split; [ exact Hlen | split; [ exact Hlenb |]]].
    intros ix Hix HL. apply HR; [ exact Hix |].
    right. split; [ reflexivity |].
    apply (live_ext_neutral [v_to_e v] K ix); [ solve [neutral_solve] | exact HL ].
Qed.

Lemma sim_local_set_bwd : forall phi K f f_o f_o' hs s j v vd es,
  f_inst f_o' = f_inst f_o ->
  N.to_nat j < length (f_locs f_o) ->
  f_locs f_o' = seq.set_nth vd (f_locs f_o) (N.to_nat j) v ->
  rel_es phi K es [v_to_e v; AI_basic (BI_local_set j)] ->
  frames_agree phi (live_ext es K) f f_o ->
  exists f' es',
    reduce hs s f es hs s f' es' /\
    rel_es phi K es' [] /\
    frames_agree phi (live_ext es' K) f' f_o'.
Proof.
  intros phi K f f_o f_o' hs s j v vd es Hinsto Hj Hlocso Hrel Hfr.
  apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e [t [Heq [He Ht]]]].
  apply rel_e_v_inv_r in He. subst e.
  apply rel_es_cons_inv_r in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
  apply rel_es_nil_inv_r in Ht1. subst t1. subst t. subst es.
  apply rel_e_basic_inv_r in He1. destruct He1 as [b [Hb1 Hb]]. subst e1.
  apply rel_b_set_inv_r in Hb. destruct Hb as [i [Hbi [Hji Hsf]]].
  subst b. subst j.
  destruct Hfr as [Hinst [Hlen [Hlenb HR]]].
  assert (Hi : N.to_nat i < length (f_locs f)) by (apply Hlenb; exact Hj).
  exists (Build_frame (seq.set_nth vd (f_locs f) (N.to_nat i) v) (f_inst f)), nil.
  split; [| split].
  - eapply r_local_set with (vd := vd); [ reflexivity | | reflexivity ].
    simpl. apply lt_to_leq. exact Hi.
  - apply rel_nil.
  - split; [| split; [| split]].
    + simpl. rewrite Hinsto. exact Hinst.
    + simpl. rewrite Hlocso.
      rewrite (length_set_nth_lt vd (f_locs f) (N.to_nat i) v Hi).
      rewrite (length_set_nth_lt vd (f_locs f_o) _ v Hj).
      exact Hlen.
    + simpl. rewrite Hlocso.
      rewrite (length_set_nth_lt vd (f_locs f) (N.to_nat i) v Hi).
      rewrite (length_set_nth_lt vd (f_locs f_o) _ v Hj).
      exact Hlenb.
    + simpl. rewrite Hlocso.
      eapply R_phi_live_set; [ | | exact Hi | exact Hj | exact HR ].
      * intros k HL' Hne. apply Hsf; [ exact HL' | exact Hne ].
      * intros k HL' Hne. right. split; [| apply (live_ext_nil K k); exact HL' ].
        simpl. destruct (live_v_to_e k v) as [_ Hk]. rewrite Hk. simpl.
        rewrite Bool.orb_false_r.
        destruct (N.eqb_spec k i) as [Heq | Hne2];
        [ exfalso; apply Hne; exact Heq | reflexivity ].
Qed.

(* ── The backward induction ───────────────────────────────────────
   The mirror image of [sim_step_store_wf].  It is a separate induction,
   not a corollary: [reduce] is not determinate, so a step of the
   optimized side cannot be reflected by running the forward simulation
   backwards.

   The [with_funcs] normal form transfers, but to the other side.
   Forward the optimized store was [with_funcs s fs]; here it is the
   *source* store that is [with_funcs s_opt fs], and every helper below
   -- the ten [*_with_funcs], the ten [*_keeps_funcs], the seven
   [*_none_wf] -- is a statement about [with_funcs] alone, so all of
   them apply unchanged.  In particular every rule that only *reads* the
   store still transfers by conversion, since [with_funcs] keeps each
   visible section syntactically.

   [store_rel_shape_l] is what puts the source store in that form: it is
   [store_rel_shape] read from the other end. *)
Lemma store_rel_shape_l : forall s s_opt,
  store_rel s s_opt -> with_funcs s_opt (s_funcs s) = s.
Proof.
  intros s s_opt [_ [Ht [Hm [Hg [He Hd]]]]].
  unfold with_funcs.
  rewrite <- Ht. rewrite <- Hm. rewrite <- Hg. rewrite <- He. rewrite <- Hd.
  destruct s. reflexivity.
Qed.

(* [store_rel_keep] the other way round: the source keeps its code while
   the optimized store steps, and the step leaves s_funcs alone. *)
Lemma store_rel_keep_bwd : forall s_opt fs s_opt',
  store_rel (with_funcs s_opt fs) s_opt -> s_funcs s_opt' = s_funcs s_opt ->
  store_rel (with_funcs s_opt' fs) s_opt'.
Proof.
  intros s_opt fs s_opt' [Hf _] Heq. split.
  - cbn [s_funcs] in *. rewrite Heq. exact Hf.
  - repeat split; reflexivity.
Qed.

(* The tactic families, mirrored.  The one systematic difference is the
   direction of the instance rewrite: [frames_agree] states
   [f_inst f = f_inst f_o], and the goal is now the *source* step, so it
   is the left-hand side that needs replacing. *)
Ltac sim_plain_bwd :=
  match goal with
  | Hrel : rel_es _ _ ?e _ |- _ =>
      apply rel_es_plain_inv_r in Hrel; [ subst e | solve [plain_solve] ]
  end;
  match goal with
  | Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 3 eexists; split; [| split; [| split]];
      [ econstructor; rewrite ? Hinst;
        first [ eassumption | reflexivity | wf_none ]
      | eassumption
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

Ltac sim_plain_rule_bwd R :=
  match goal with
  | Hrel : rel_es _ _ ?e _ |- _ =>
      apply rel_es_plain_inv_r in Hrel; [ subst e | solve [plain_solve] ]
  end;
  match goal with
  | Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 3 eexists; split; [| split; [| split]];
      [ eapply R; rewrite ? Hinst;
        first [ eassumption | reflexivity | wf_none ]
      | eassumption
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

Ltac sim_storeop_bwd R Lwf Lkf :=
  match goal with
  | Hrel : rel_es _ _ ?e _ |- _ =>
      apply rel_es_plain_inv_r in Hrel; [ subst e | solve [plain_solve] ]
  end;
  match goal with
  | Hst : store_rel (with_funcs _ _) _, Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 3 eexists; split; [| split; [| split]];
      [ eapply R; rewrite ? Hinst;
        first [ apply Lwf; eassumption | eassumption | reflexivity ]
      | eapply store_rel_keep_bwd; [ exact Hst | eapply Lkf; eassumption ]
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

(* The call_indirect replays, from the optimized side.  Same scripts as
   [reduce_call_indirect_success_wf] and its failure sibling with the
   store lookup read backwards. *)
Lemma reduce_call_indirect_success_bwd :
  forall hs s_opt fs f_o v x y a f,
    store_rel (with_funcs s_opt fs) s_opt ->
    reduce hs s_opt f_o [v_to_e v; AI_basic (BI_call_indirect x y)]
           hs s_opt f_o [AI_invoke a] ->
    f_inst f = f_inst f_o ->
    reduce hs (with_funcs s_opt fs) f
             [v_to_e v; AI_basic (BI_call_indirect x y)]
           hs (with_funcs s_opt fs) f [AI_invoke a].
Proof.
  intros hs s_opt fs f_o v x y a f Hst Hred.
  revert f.
  remember [v_to_e v; AI_basic (BI_call_indirect x y)] as e eqn:He.
  remember [AI_invoke a] as e' eqn:He'.
  revert Hst.
  induction Hred; intros Hst f_src Hinst; try (inversion He); try (discriminate He').
  - apply r_simple. rewrite He in H. exact H.
  - subst x0 y0.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H0) as [cl_s [Hlk Hfi]].
    eapply r_call_indirect_success;
      [ rewrite Hinst; exact H
      | exact Hlk
      | rewrite Hinst; rewrite <- (funcinst_rel_type _ _ Hfi); exact H1 ].
  - assert (Hin : In (AI_invoke a0) [v_to_e v; AI_basic (BI_call_indirect x y)]).
    { rewrite <- He. apply in_or_app. right. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [Hv | Hinv].
    + destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
      destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
    + destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs].
  - rewrite He in H. rewrite He' in H0.
    assert (Hfill : es = [v_to_e v; AI_basic (BI_call_indirect x y)]
                    /\ es' = [AI_invoke a]).
    { eapply lfill_singleton_invert; [exact H | exact H0 | | ].
      { intro Hm. destruct v as [vn | vv | r]; compute in Hm; try discriminate Hm.
        destruct r as [t | fa | ea]; compute in Hm; discriminate Hm. }
      { intro Hc. cbv in Hc. discriminate Hc. } }
    destruct Hfill as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hst | exact Hinst].
Qed.

Lemma reduce_call_indirect_failure_bwd :
  forall hs s_opt fs f_o v x y f,
    store_rel (with_funcs s_opt fs) s_opt ->
    reduce hs s_opt f_o [v_to_e v; AI_basic (BI_call_indirect x y)]
           hs s_opt f_o [AI_trap] ->
    f_inst f = f_inst f_o ->
    reduce hs (with_funcs s_opt fs) f
             [v_to_e v; AI_basic (BI_call_indirect x y)]
           hs (with_funcs s_opt fs) f [AI_trap].
Proof.
  intros hs s_opt fs f_o v x y f Hst Hred.
  revert f.
  remember [v_to_e v; AI_basic (BI_call_indirect x y)] as e eqn:He.
  remember [AI_trap] as e' eqn:He'.
  revert Hst.
  induction Hred; intros Hst f_src Hinst; try (inversion He); try (discriminate He').
  - apply r_simple. rewrite He in H. exact H.
  - subst x0 y0.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H0) as [cl_s [Hlk Hfi]].
    eapply r_call_indirect_failure_mismatch;
      [ rewrite Hinst; exact H
      | exact Hlk
      | rewrite Hinst; rewrite <- (funcinst_rel_type _ _ Hfi); exact H1 ].
  - subst x0 y0. eapply r_call_indirect_failure_bound;
      rewrite Hinst; exact H.
  - subst x0 y0. eapply r_call_indirect_failure_null_ref;
      rewrite Hinst; exact H.
  - assert (Hin : In (AI_invoke a) [v_to_e v; AI_basic (BI_call_indirect x y)]).
    { rewrite <- He. apply in_or_app. right. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [Hv | Hinv].
    + destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
      destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
    + destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs].
  - assert (Hin : In (AI_invoke a) [v_to_e v; AI_basic (BI_call_indirect x y)]).
    { rewrite <- He. apply in_or_app. right. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [Hv | Hinv].
    + destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
      destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
    + destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs].
  - rewrite He in H. rewrite He' in H0.
    assert (Hfill : es = [v_to_e v; AI_basic (BI_call_indirect x y)]
                    /\ es' = [AI_trap]).
    { eapply lfill_singleton_invert; [exact H | exact H0 | | ].
      { intro Hm. destruct v as [vn | vv | r]; compute in Hm; try discriminate Hm.
        destruct r as [t | fa | ea]; compute in Hm; discriminate Hm. }
      { intro Hc. cbv in Hc. discriminate Hc. } }
    destruct Hfill as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hst | exact Hinst].
Qed.

Theorem sim_step_store_bwd_wf : forall hs s_opt f_o es_o hs' s_opt' f_o' es_o',
  reduce hs s_opt f_o es_o hs' s_opt' f_o' es_o' ->
  host_ok ->
  forall fs phi K f X,
    store_rel (with_funcs s_opt fs) s_opt ->
    rel_es phi K X es_o ->
    frames_agree phi (live_ext X K) f f_o ->
    exists s' f' X',
      reduce hs (with_funcs s_opt fs) f X hs' s' f' X' /\
      store_rel s' s_opt' /\
      rel_es phi K X' es_o' /\
      frames_agree phi (live_ext X' K) f' f_o'.
Proof.
  intros hs s_opt f_o es_o hs' s_opt' f_o' es_o' Hred Hhost.
  induction Hred; intros fs phi K f_s X Hst Hrel Hfr.
  all: try (solve [ sim_plain_bwd ]).
  all: try (solve [ sim_plain_rule_bwd r_table_get_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_table_set_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_table_grow_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_load_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_load_packed_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_load_vec_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_load_vec_lane_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_store_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_store_packed_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_store_vec_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_store_vec_lane_failure ]).
  all: try (solve [ sim_plain_rule_bwd r_memory_grow_failure ]).
  all: try (solve [ sim_storeop_bwd r_global_set supdate_glob_with_funcs
                                    supdate_glob_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_table_set_success stab_update_with_funcs
                                    stab_update_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_table_grow_success stab_grow_with_funcs
                                    stab_grow_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_elem_drop selem_drop_with_funcs
                                    selem_drop_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_data_drop sdata_drop_with_funcs
                                    sdata_drop_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_store_success smem_store_with_funcs
                                    smem_store_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_store_packed_success
                                    smem_store_packed_with_funcs
                                    smem_store_packed_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_store_vec_success smem_store_vec_with_funcs
                                    smem_store_vec_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_store_vec_lane_success
                                    smem_store_vec_lane_with_funcs
                                    smem_store_vec_lane_keeps_funcs ]).
  all: try (solve [ sim_storeop_bwd r_memory_grow_success smem_grow_with_funcs
                                    smem_grow_keeps_funcs ]).
  { (* r_simple *)
    destruct (sim_simple_bwd _ _ H phi K X Hrel) as [X' [Hrs [Hrel' Hsub]]].
    exists (with_funcs s fs), f_s, X'. split; [| split; [| split]].
    - apply r_simple. exact Hrs.
    - exact Hst.
    - exact Hrel'.
    - exact (frames_agree_sub _ _ _ _ _ Hsub Hfr).
  }
  { (* r_block *)
    apply rel_es_split_r in Hrel.
    destruct Hrel as [X1 [X2 [HeqX [Hr1 Hr2]]]].
    apply rel_es_plain_inv_r in Hr1; [| apply es_plain_const_list; assumption ].
    subst X1.
    apply rel_es_cons_inv_r in Hr2. destruct Hr2 as [e_s [t_s [Heq2 [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t_s. subst X2. subst X.
    apply rel_e_basic_inv_r in He. destruct He as [b_s [Hbs0 Hb]]. subst e_s.
    apply rel_b_block_inv_r in Hb. destruct Hb as [bs [Hbo2 [Hbw Hbs]]].
    subst b_s.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_block; [ rewrite Hinst; eassumption | eassumption
                      | eassumption | eassumption | eassumption ].
    - exact Hst.
    - apply rel_cons; [| apply rel_nil ].
      apply rel_label.
      + destruct Hbw as [Hbr | Hbw].
        * apply label_ok_nobr. rewrite es_br_cat.
          rewrite const_list_nobr; [| assumption ].
          rewrite bs_br_to_e_list. rewrite Hbr. reflexivity.
        * apply label_ok_nohazard. rewrite es_hazard_app.
          rewrite es_hazard_const; [| assumption ].
          rewrite es_hazard_to_e_list. rewrite Hbw. reflexivity.
      + apply rel_nil.
      + apply rel_es_app.
        * apply rel_es_plain. apply es_plain_const_list. assumption.
        * eapply rel_es_weaken; [ apply rel_es_to_e_list; exact Hbs |].
          intros i [Habs | Hk]; [ discriminate Habs | exact Hk ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl.
      rewrite live_ext_label_nil in Hl.
      rewrite live_ext_const_app in Hl; [| assumption ].
      rewrite live_ext_to_e_list in Hl.
      rewrite live_ext_const_app; [| assumption ].
      rewrite live_ext_block.
      unfold bs_live_ext in Hl.
      destruct Hl as [H' | [_ H']]; [ left; exact H' | right; exact H' ].
  }
  { (* r_loop *)
    apply rel_es_split_r in Hrel.
    destruct Hrel as [X1 [X2 [HeqX [Hr1 Hr2]]]].
    apply rel_es_plain_inv_r in Hr1; [| apply es_plain_const_list; assumption ].
    subst X1.
    apply rel_es_cons_inv_r in Hr2. destruct Hr2 as [e_s [t_s [Heq2 [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t_s. subst X2. subst X.
    apply rel_e_basic_inv_r in He. destruct He as [b_s [Hbs0 Hb]]. subst e_s.
    apply rel_b_loop_inv_r in Hb. destruct Hb as [bs [Hbo2 [Hnw Hbs]]]. subst b_s.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_loop; [ rewrite Hinst; eassumption | eassumption
                     | eassumption | eassumption | eassumption ].
    - exact Hst.
    - apply rel_cons; [| apply rel_nil ].
      apply rel_label.
      + destruct Hnw as [Hbr | Hnw'].
        * apply label_ok_nobr. rewrite es_br_cat.
          rewrite const_list_nobr; [| assumption ].
          rewrite bs_br_to_e_list. rewrite Hbr. reflexivity.
        * apply label_ok_nohazard. rewrite es_hazard_app.
          rewrite es_hazard_const; [| assumption ].
          rewrite es_hazard_to_e_list. rewrite Hnw'. reflexivity.
      + apply rel_cons; [| apply rel_nil ].
        apply rel_basic. apply relb_loop; [ exact Hnw |].
        eapply rel_bs_weaken; [ exact Hbs |].
        intros i [Hl | Hl]; [ left; exact Hl |].
        right. rewrite ! live_ext_nil in Hl. rewrite ! live_ext_nil. exact Hl.
      + apply rel_es_app.
        * apply rel_es_plain. apply es_plain_const_list. assumption.
        * eapply rel_es_weaken; [ apply rel_es_to_e_list; exact Hbs |].
          intros i [Hl | Hl]; [| right; exact Hl ].
          left. rewrite es_live_singleton in Hl. cbn [ai_live] in Hl.
          rewrite bi_live_loop in Hl. exact Hl.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl.
      rewrite live_ext_label in Hl.
      rewrite live_ext_const_app in Hl; [| assumption ].
      rewrite live_ext_to_e_list in Hl.
      rewrite live_ext_const_app; [| assumption ].
      rewrite live_ext_loop.
      unfold bs_live_ext in Hl.
      rewrite es_live_singleton in Hl. cbn [ai_live] in Hl.
      rewrite bi_live_loop in Hl.
      destruct Hl as [H' | [_ [H' | H']]];
        [ left; exact H' | left; exact H' | right; exact H' ].
  }
  { (* r_call_indirect_success *)
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H0) as [cl_s [Hlk Hfi]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_call_indirect_success.
      + rewrite Hinst. exact H.
      + exact Hlk.
      + rewrite Hinst. rewrite <- (funcinst_rel_type _ _ Hfi). exact H1.
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_call_indirect_failure_mismatch *)
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H0) as [cl_s [Hlk Hfi]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_call_indirect_failure_mismatch.
      + rewrite Hinst. exact H.
      + exact Hlk.
      + rewrite Hinst. rewrite <- (funcinst_rel_type _ _ Hfi). exact H1.
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call *)
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - apply r_return_call. eapply reduce_call_transport;
        [ exact Hred | exact Hinst ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call_indirect_success *)
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - apply r_return_call_indirect_success.
      eapply reduce_call_indirect_success_bwd;
        [ exact Hst | exact Hred | exact Hinst ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call_indirect_failure *)
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    pose proof (proj1 Hfr) as Hinst.
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - apply r_return_call_indirect_failure.
      eapply reduce_call_indirect_failure_bwd;
        [ exact Hst | exact Hred | exact Hinst ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_invoke_native: the source enters the [code] that funcinst_rel
       hands back for the optimized [code_opt] the rule entered. *)
    subst ves. subst cl. subst code.
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    pose proof (proj1 Hfr) as Hinst.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H) as [cl_s [Hlk Hfi]].
    destruct cl_s as [tf_s inst_s code_s | tf_s h_s]; simpl in Hfi;
      [| discriminate Hfi ].
    destruct tf_s as [tsa tsb].
    destruct Hfi as [co [Hco Hcr]].
    injection Hco as Hta Htb Hinst2 Hcode2.
    subst tsa. subst tsb. subst inst_s. subst co.
    destruct code_s as [xs tss ess].
    destruct Hcr as [Hty [Hloc [psi [Hbody Hentry]]]].
    cbn in Hty, Hloc, Hbody, Hentry.
    subst xs.
    (* the optimized callee ran, so its locals are defaultable; code_rel
       transfers that to the source's, which declares more of them *)
    destruct (defaults_of_not_none tss
                (fun Habs => ltac:(rewrite (proj1 Hloc Habs) in H7;
                                   discriminate H7)))
      as [defaults_s Hds].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_invoke_native;
        [ exact Hlk | reflexivity | reflexivity | reflexivity
        | eassumption | reflexivity | eassumption | eassumption
        | exact Hds ].
    - exact Hst.
    - apply rel_cons; [| apply rel_nil ].
      eapply rel_frame.
      + apply (Hentry inst vs defaults_s defaults _);
          [ congruence | exact Hds | exact H7 ].
      + apply rel_cons; [| apply rel_nil ].
        apply rel_label; [| apply rel_nil |].
        * apply label_ok_dead; [ reflexivity |].
          intros i Hi. rewrite ! live_ext_nil in Hi. exact Hi.
        * eapply rel_es_weaken; [ apply rel_es_to_e_list; exact Hbody |].
          intros i [Habs | Habs];
            [ discriminate Habs | rewrite live_ext_nil in Habs; exact Habs ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl. rewrite live_ext_frame in Hl.
      apply live_ext_neutral_bwd; [ solve [neutral_solve] | exact Hl ].
  }
  { (* r_invoke_host_success: host_transports_bwd supplies the source
       successor store, and with it the relation *)
    subst ves. subst cl.
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H) as [cl_s [Hlk Hfi]].
    destruct cl_s as [tf_s inst_s code_s | tf_s h_s]; simpl in Hfi.
    { destruct tf_s as [tsa tsb]. destruct Hfi as [co [Hco _]].
      discriminate Hco. }
    injection Hfi as Htf Hh. subst tf_s. subst h_s.
    destruct Hhost as [_ [Htrb _]].
    destruct (Htrb _ _ _ _ _ _ _ _ _ Hst H5) as [s_s' [Happ Hst']].
    exists s_s'. eexists. eexists. split; [| split; [| split]].
    - eapply r_invoke_host_success;
        [ exact Hlk | reflexivity | reflexivity | eassumption
        | eassumption | eassumption | exact Happ ].
    - exact Hst'.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_invoke_host_diverge *)
    subst ves. subst cl.
    apply rel_es_plain_inv_r in Hrel; [| solve [plain_solve] ]. subst X.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H) as [cl_s [Hlk Hfi]].
    destruct cl_s as [tf_s inst_s code_s | tf_s h_s]; simpl in Hfi.
    { destruct tf_s as [tsa tsb]. destruct Hfi as [co [Hco _]].
      discriminate Hco. }
    injection Hfi as Htf Hh. subst tf_s. subst h_s.
    destruct Hhost as [_ [_ Htrap]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_invoke_host_diverge;
        [ exact Hlk | reflexivity | reflexivity | eassumption
        | eassumption | eassumption
        | exact (proj2 (Htrap _ _ _ _ _ _ _ Hst) H5) ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_invoke *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e_s [t_s [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t_s. subst X.
    apply rel_e_frame_inv_r in He.
    destruct He as [fr_s [esf_s [psi [Hfo [Hfa Hes]]]]]. subst e_s.
    subst es. apply rel_es_lfill_inv_r in Hes.
    destruct Hes as [lh_s [hole_s [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv_r in Hhole; [| solve [plain_solve] ]. subst hole_s.
    subst esf_s.
    destruct (store_rel_lookup_bwd _ _ _ _ Hst H) as [cl_s [Hlk Hfi]].
    exists (with_funcs s fs). eexists. eexists. split; [| split; [| split]].
    - eapply r_return_invoke;
        [ exact Hlk | rewrite <- (funcinst_rel_type _ _ Hfi); exact H0
        | eassumption | eassumption | eassumption | eassumption
        | reflexivity ].
    - exact Hst.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl); solve [neutral_solve].
  }
  { (* r_local_get: neither side touches the store *)
    destruct (sim_local_get_bwd phi K f_s f hs (with_funcs s fs) j v X
                H Hrel Hfr)
      as [f_s' [X' [Hr [Hrel' Hfr']]]].
    exists (with_funcs s fs), f_s', X'.
    split; [exact Hr | split; [exact Hst | split; [exact Hrel' | exact Hfr']]].
  }
  { (* r_local_set *)
    destruct (sim_local_set_bwd phi K f_s f f' hs (with_funcs s fs) i v vd X
                H (leq_to_lt _ _ H0) H1 Hrel Hfr)
      as [f_s' [X' [Hr [Hrel' Hfr']]]].
    exists (with_funcs s fs), f_s', X'.
    split; [exact Hr | split; [exact Hst | split; [exact Hrel' | exact Hfr']]].
  }
  { (* r_label *)
    try subst les les'.
    apply rel_es_lfill_inv_r in Hrel.
    destruct Hrel as [lh_s [hole_s [Hheq [Hlh [Hok Hhole]]]]]. subst X.
    destruct (IHHred fs phi (lh_K lh_s K) f_s hole_s Hst Hhole
                (frames_agree_sub _ _ _ _ _
                   (fun i Hi => proj2 (live_ext_lfill _ lh_s hole_s K i) Hi) Hfr))
      as [s_s' [f_s' [hole_s' [Hr [Hst' [Hrel' Hfr']]]]]].
    exists s_s', f_s', (lfill lh_s hole_s'). split; [| split; [| split]].
    - eapply r_label; [ exact Hr | reflexivity | reflexivity ].
    - exact Hst'.
    - apply rel_es_lfill; [ exact Hlh | | exact Hrel' ].
      eapply lh_labels_ok_step; [ exact Hr | exact Hok ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr').
      intros i Hi. apply live_ext_lfill. exact Hi.
  }
  { (* r_frame *)
    apply rel_es_cons_inv_r in Hrel. destruct Hrel as [e_s [t_s [Heq [He Ht]]]].
    apply rel_es_nil_inv_r in Ht. subst t_s. subst X.
    apply rel_e_frame_inv_r in He.
    destruct He as [fr_s [esf_s [psi [Hfo [Hfa Hes]]]]]. subst e_s.
    assert (Hin : frames_agree psi (live_ext esf_s (fun _ => False)) fr_s f).
    { refine (frames_agree_sub _ _ _ _ _ _ Hfa).
      intros ix Hi. unfold live_ext, es_live in *.
      destruct Hi as [H' | [_ Hf]]; [ exact H' | destruct Hf ]. }
    destruct (IHHred fs psi (fun _ => False) fr_s esf_s Hst Hes Hin)
      as [s_s' [fr_s' [esf_s' [Hr [Hst' [Hrel' Hfa']]]]]].
    exists s_s'. eexists. eexists. split; [| split; [| split]].
    - apply r_frame. exact Hr.
    - exact Hst'.
    - apply rel_cons; [| apply rel_nil ].
      eapply rel_frame; [| exact Hrel' ].
      refine (frames_agree_sub _ _ _ _ _ _ Hfa').
      intros i Hi. left. exact Hi.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl. apply live_ext_frame. apply live_ext_frame in Hl. exact Hl.
  }
Qed.

Theorem sim_step_store_bwd : forall hs s_opt f_o es_o hs' s_opt' f_o' es_o',
  reduce hs s_opt f_o es_o hs' s_opt' f_o' es_o' ->
  host_ok ->
  forall s phi K f es,
    store_rel s s_opt ->
    rel_es phi K es es_o ->
    frames_agree phi (live_ext es K) f f_o ->
    exists s' f' es',
      reduce hs s f es hs' s' f' es' /\
      store_rel s' s_opt' /\
      rel_es phi K es' es_o' /\
      frames_agree phi (live_ext es' K) f' f_o'.
Proof.
  intros hs s_opt f_o es_o hs' s_opt' f_o' es_o' Hred Hhost s phi K f es
         Hst Hrel Hfr.
  pose proof (store_rel_shape_l _ _ Hst) as Hshape.
  rewrite <- Hshape. rewrite <- Hshape in Hst.
  exact (sim_step_store_bwd_wf _ _ _ _ _ _ _ _ Hred Hhost _ phi K f es
           Hst Hrel Hfr).
Qed.

(* ── 4. Closure over reduce_trans ─────────────────────────────────
   The same induction as [sim_trans], with [store_rel] threaded in
   place of the [store_guarded] side condition.  Nothing new happens;
   these are transcriptions once the single-step versions are in. *)

Definition sim_cfg_store (phi : local_map) (K : N -> Prop)
    (c c_o : host_state * store_record * frame * list administrative_instruction)
    : Prop :=
  let '(hs, s, f, es) := c in
  let '(hs_o, s_o, f_o, es_o) := c_o in
  hs = hs_o /\ store_rel s s_o /\ rel_es phi K es es_o
  /\ frames_agree phi (live_ext es K) f f_o.

Theorem sim_trans_store : forall phi K,
  host_ok ->
  forall c c', reduce_trans c c' ->
    forall c_o, sim_cfg_store phi K c c_o ->
    exists c_o', reduce_trans c_o c_o' /\ sim_cfg_store phi K c' c_o'.
Proof.
  intros phi K Hhost c c' Hred.
  induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz]; intros c_o Hsim.
  - destruct x as [[[hs s] f] es]. destruct y as [[[hs' s'] f'] es'].
    destruct c_o as [[[hs_o s_o] f_o] es_o].
    destruct Hsim as [Hhs [Hst [Hrel Hfr]]]. subst hs_o.
    simpl in Hstep.
    destruct (sim_step_store _ _ _ _ _ _ _ _ Hstep Hhost s_o phi K f_o es_o
                Hst Hrel Hfr)
      as [s_o' [f_o' [es_o' [Hstep_o [Hst' [Hrel' Hfr']]]]]].
    exists (hs', s_o', f_o', es_o'). split.
    + apply Relation_Operators.rt_step. simpl. exact Hstep_o.
    + simpl. exact (conj eq_refl (conj Hst' (conj Hrel' Hfr'))).
  - exists c_o. split; [apply Relation_Operators.rt_refl | exact Hsim].
  - destruct (IHxy c_o Hsim) as [c_mid [Hfst Hsimmid]].
    destruct (IHyz c_mid Hsimmid) as [c_o' [Hsnd Hsim']].
    exists c_o'. split; [| exact Hsim'].
    eapply Relation_Operators.rt_trans; [exact Hfst | exact Hsnd].
Qed.

Theorem sim_trans_store_bwd : forall phi K,
  host_ok ->
  forall c_o c_o', reduce_trans c_o c_o' ->
    forall c, sim_cfg_store phi K c c_o ->
    exists c', reduce_trans c c' /\ sim_cfg_store phi K c' c_o'.
Proof.
  intros phi K Hhost c_o c_o' Hred.
  induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz]; intros c Hsim.
  - destruct x as [[[hs s_o] f_o] es_o]. destruct y as [[[hs' s_o'] f_o'] es_o'].
    destruct c as [[[hs_1 s] f] es].
    destruct Hsim as [Hhs [Hst [Hrel Hfr]]]. subst hs_1.
    simpl in Hstep.
    destruct (sim_step_store_bwd _ _ _ _ _ _ _ _ Hstep Hhost s phi K f es
                Hst Hrel Hfr)
      as [s' [f' [es' [Hstep_s [Hst' [Hrel' Hfr']]]]]].
    exists (hs', s', f', es'). split.
    + apply Relation_Operators.rt_step. simpl. exact Hstep_s.
    + simpl. exact (conj eq_refl (conj Hst' (conj Hrel' Hfr'))).
  - exists c. split; [apply Relation_Operators.rt_refl | exact Hsim].
  - destruct (IHxy c Hsim) as [c_mid [Hfst Hsimmid]].
    destruct (IHyz c_mid Hsimmid) as [c' [Hsnd Hsim']].
    exists c'. split; [| exact Hsim'].
    eapply Relation_Operators.rt_trans; [exact Hfst | exact Hsnd].
Qed.

(* ── 5. Terminal transfer ─────────────────────────────────────────
   A finished thread mentions no locals and no code, so a related pair
   of finished threads is an equal pair.  Both halves follow from the
   inversion lemmas already in coalesce_locals_correct.v
   ([rel_es_v_to_e_list_inv] for a value stack, [rel_e]'s [rel_trap]
   for a trap); this is the small one. *)

Lemma rel_es_terminal : forall phi K es es_o,
  rel_es phi K es es_o -> terminal es -> es_o = es.
Proof.
  intros phi K es es_o Hrel [[rvs Hvs] | Htrap]; subst es.
  - exact (rel_es_v_to_e_list_inv _ _ _ _ Hrel).
  - inversion Hrel; subst. inversion H3; subst. inversion H5; subst.
    reflexivity.
Qed.

Lemma rel_es_terminal_bwd : forall phi K es es_o,
  rel_es phi K es es_o -> terminal es_o -> es = es_o.
Proof.
  intros phi K es es_o Hrel [[rvs Hvs] | Htrap]; subst es_o.
  - exact (rel_es_v_to_e_list_inv_r _ _ _ _ Hrel).
  - inversion Hrel; subst. inversion H4; subst. inversion H5; subst.
    reflexivity.
Qed.

(* ── 6. Frames with no locals ─────────────────────────────────────
   [call_equiv] runs both sides from the *same* frame and requires both
   to finish in that same frame.  The instantiation frame has no
   locals, and no rule changes the length of [f_locs] or the instance,
   so an empty frame stays empty and the two runs' final frames are
   literally equal.  Only r_local_set touches f_locs at all, and it
   writes in range. *)

Lemma reduce_locs_length : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' -> length (f_locs f') = length (f_locs f).
Proof.
  intros hs s f es hs' s' f' es' Hred.
  induction Hred; try reflexivity; try assumption.
  rewrite H1. apply length_set_nth_lt. apply leq_to_lt. exact H0.
Qed.

Lemma reduce_inst : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' -> f_inst f' = f_inst f.
Proof.
  intros hs s f es hs' s' f' es' Hred.
  induction Hred; try reflexivity; try assumption.
Qed.

Lemma reduce_trans_frame : forall c c',
  reduce_trans c c' ->
  length (f_locs (cfg_frame c')) = length (f_locs (cfg_frame c)) /\
  f_inst (cfg_frame c') = f_inst (cfg_frame c).
Proof.
  intros c c' Hred.
  induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - destruct x as [[[hs s] f] es]. destruct y as [[[hs' s'] f'] es'].
    simpl in *. split.
    + eapply reduce_locs_length; eassumption.
    + eapply reduce_inst; eassumption.
  - split; reflexivity.
  - destruct IHxy as [H1 H2]. destruct IHyz as [H3 H4].
    split; [rewrite H3; exact H1 | rewrite H4; exact H2].
Qed.

Lemma reduce_trans_frame_nil : forall hs s f es hs' s' f' es',
  f_locs f = [] ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  f' = f.
Proof.
  intros hs s f es hs' s' f' es' Hnil Hred.
  destruct (reduce_trans_frame _ _ Hred) as [Hlen Hinst]. simpl in Hlen, Hinst.
  rewrite Hnil in Hlen. simpl in Hlen.
  apply length_zero_iff_nil in Hlen.
  destruct f as [locs inst]. destruct f' as [locs' inst'].
  simpl in *. subst locs'. subst inst'. rewrite Hnil. reflexivity.
Qed.

(* ── 7. Forward and backward call equivalence ─────────────────────
   With the pieces above this is glue: the initial instruction list
   [v_to_e_list vs ++ [AI_invoke a]] relates to itself under any map
   (values and [AI_invoke] are fixed points of [rel_e]), the empty
   frame agrees with itself, the simulation runs, terminal transfer
   turns the related result into an equal one, and [store_rel] gives
   the [store_visible_eq] the specification asks for. *)

Lemma rel_es_invoke_args : forall phi K vs a,
  rel_es phi K (v_to_e_list vs ++ [AI_invoke a]) (v_to_e_list vs ++ [AI_invoke a]).
Proof.
  intros phi K vs a. apply rel_es_app.
  - apply rel_es_v_to_e_list.
  - apply rel_cons; [apply rel_invoke | apply rel_nil].
Qed.

Lemma call_equiv_from_store_rel : forall s s_opt f,
  host_ok ->
  store_rel s s_opt ->
  f_locs f = [] ->
  call_equiv s s_opt f f.
Proof.
  intros s s_opt f Hhost Hrel Hnil a vs hs hs' res Hterm.
  assert (Hsim0 : sim_cfg_store empty (fun _ => False)
                    (hs, s, f, v_to_e_list vs ++ [AI_invoke a])
                    (hs, s_opt, f, v_to_e_list vs ++ [AI_invoke a])).
  { simpl. refine (conj eq_refl (conj Hrel (conj _ _))).
    - apply rel_es_invoke_args.
    - apply frames_agree_empty_refl. }
  split.
  { intros s' Hred.
    destruct (sim_trans_store empty (fun _ => False) Hhost _ _ Hred _ Hsim0)
      as [c_o' [Hred_o Hsim']].
    destruct c_o' as [[[hs_o' s_opt'] f_o'] es_o'].
    destruct Hsim' as [Hhs [Hst [Hrel' Hfr']]]. subst hs_o'.
    pose proof (rel_es_terminal _ _ _ _ Hrel' Hterm) as Heq. subst es_o'.
    pose proof (reduce_trans_frame_nil _ _ _ _ _ _ _ _ Hnil Hred_o) as Hf.
    subst f_o'.
    exists s_opt'. split; [exact Hred_o | exact (proj2 Hst)]. }
  { intros s_opt' Hred_o.
    destruct (sim_trans_store_bwd empty (fun _ => False) Hhost _ _ Hred_o _ Hsim0)
      as [c' [Hred Hsim']].
    destruct c' as [[[hs_1 s'] f_src'] es_src'].
    destruct Hsim' as [Hhs [Hst [Hrel' Hfr']]]. subst hs_1.
    pose proof (rel_es_terminal_bwd _ _ _ _ Hrel' Hterm) as Heq. subst es_src'.
    pose proof (reduce_trans_frame_nil _ _ _ _ _ _ _ _ Hnil Hred) as Hf.
    subst f_src'.
    exists s'. split; [exact Hred | exact (proj2 Hst)]. }
Qed.

(* The unsupported module is returned untouched, so the two sides are
   the same store and the same frame. *)
Lemma call_equiv_refl : forall s f, call_equiv s s f f.
Proof.
  intros s f a vs hs hs' res Hterm. split.
  - intros s' Hred. exists s'. split; [exact Hred |].
    repeat split; reflexivity.
  - intros s_opt' Hred. exists s_opt'. split; [exact Hred |].
    repeat split; reflexivity.
Qed.

(* ── 8. The assembly ──────────────────────────────────────────────
   This is the statement in toplevel_spec.v, and
   it follows from the lemmas above by splitting on whether the pass
   accepts the module.  An unsupported module comes back untouched, so
   the two sides are literally the same run.  A supported one
   instantiates to a related store, in the same instance and hence the
   same frame, and [call_equiv_from_store_rel] does the rest. *)

(* [coalesce_module_correct_statement], [host_ignores_code] and
   [store_guarded] are in toplevel_spec.v: they are part of what is
   claimed, so they belong with the claim rather than with the proof.

   This is the same conclusion under [host_ok], the form the simulation
   actually consumes.  It is the general one -- see [host_ignores_code_ok]
   below for why the headline uses the other. *)
Theorem coalesce_module_correct_host_ok :
  host_ok ->
  forall (s : store_record) (m : module) (v_imps : list extern_value)
         (s_end : store_record) (f : frame) (bes : list basic_instruction),
    store_guarded s ->
    instantiate s m v_imps (s_end, f, bes) ->
    exists s_end_opt f_opt bes_opt,
      instantiate s (coalesce_module m) v_imps (s_end_opt, f_opt, bes_opt) /\
      call_equiv s_end s_end_opt f f_opt.
Proof.
  intros Hhost s m v_imps s_end f bes Hg Hinst.
  destruct (module_supported m) eqn:Hsup.
  - destruct (coalesce_instantiate s m v_imps s_end f bes Hsup Hg Hinst)
      as [s_end_opt [Hinst_opt Hrel]].
    exists s_end_opt, f, bes. split; [exact Hinst_opt |].
    apply call_equiv_from_store_rel; [exact Hhost | exact Hrel |].
    (* the instantiation frame has no locals: instantiate fixes
       f = {| f_locs := []; f_inst := inst |} *)
    destruct Hinst as [t_imps_mod [t_imps [t_exps [hs' [inst [g_inits
      [r_inits [_ [_ [_ [_ [_ [_ [Hf _]]]]]]]]]]]]]].
    rewrite Hf. reflexivity.
  - rewrite (coalesce_module_unsupported_id m Hsup).
    exists s_end, f, bes. split; [exact Hinst | apply call_equiv_refl].
Qed.

(* [host_ok] is the shape the simulation wants: it is stated over
   [store_rel], because that is what has to be re-established after a host
   call.  [store_rel] is pass-internal, though, so an embedder cannot read
   that assumption off toplevel_spec.v and check it.

   [host_ignores_code] is the shape an embedder can check -- it mentions
   only [store_visible_eq] -- and it is sufficient.  The bridge is the
   observation that if the host leaves [s_funcs] alone on both sides, then
   the [Forall2 funcinst_rel] half of [store_rel] survives the call
   unchanged, and the visible half is transported by assumption.

   It is sufficient, not equivalent: [host_ok] would also permit a host
   that installs *related* code on the two sides, which no embedder could
   sensibly be asked to promise.  Both theorems are kept, so nothing is
   lost by stating the headline with the weaker-looking hypothesis. *)
Lemma host_ignores_code_ok : host_ignores_code -> host_ok.
Proof.
  intros [Hsome Hnone]. split; [| split].
  - intros hs s s_opt tf h vcs hs' s' r [Hf Hvis] Happ.
    destruct (Hsome _ _ _ _ _ _ _ _ _ Hvis Happ)
      as [s_opt' [Happ' [Hvis' [He1 He2]]]].
    exists s_opt'. split; [exact Happ' |].
    split; [ rewrite He1; rewrite He2; exact Hf | exact Hvis' ].
  - intros hs s s_opt tf h vcs hs' s_opt' r [Hf Hvis] Happ.
    destruct (Hsome _ _ _ _ _ _ _ _ _ (store_visible_eq_sym _ _ Hvis) Happ)
      as [s' [Happ' [Hvis' [He1 He2]]]].
    exists s'. split; [exact Happ' |].
    split; [ rewrite He1; rewrite He2; exact Hf
           | apply store_visible_eq_sym; exact Hvis' ].
  - intros hs s s_opt tf h vcs hs' [_ Hvis]. split.
    + intros H. exact (Hnone _ _ _ _ _ _ _ Hvis H).
    + intros H. exact (Hnone _ _ _ _ _ _ _ (store_visible_eq_sym _ _ Hvis) H).
Qed.

(* The headline.  Its type is a single name from toplevel_spec.v, where
   that name is spelled out in full -- so the statement being claimed is
   read off one place, not assembled from this file and that one. *)
Theorem coalesce_module_correct : coalesce_module_correct_statement.
Proof.
  unfold coalesce_module_correct_statement.
  intros H. apply coalesce_module_correct_host_ok.
  apply host_ignores_code_ok. exact H.
Qed.

End TopLevelCorrect.
