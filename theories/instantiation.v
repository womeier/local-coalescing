(** The store relation, and that the coalesced module builds one.

    This is the half of the top-level proof that never runs any code.
    It says what it means for two stores to be related, proves that the
    coalesced module still validates, and proves that instantiating it
    reaches the same instance and a related store.  [toplevel_correct.v]
    picks up from there: it shows the simulation *preserves* the
    relation, and assembles the two halves into the specification.

    The split is along a real seam.  Nothing here mentions [rel_es],
    [frames_agree] or a single [reduce] step of user code -- the only
    reductions are the initializer runs, and those are constant
    expressions.  Nothing in [toplevel_correct.v] mentions
    [module_typing] or [alloc_module].

    Three things are shared and therefore live here, since this file
    comes first: [store_rel] and the two relations it is built from,
    [with_funcs], and the [cfg_*] configuration projections.  The
    [with_funcs] *transfer suite* -- the thirty-odd lemmas saying each
    store operation ignores [s_funcs] -- is simulation machinery and
    stays in [toplevel_correct.v]. *)

From Wasm Require Import datatypes datatypes_properties opsem properties
                         typing instantiation_spec.
From Stdlib Require Import List Lia.
From Wasmopt Require Import coalesce_locals coalesce_locals_correct
                            alloc_correct toplevel_spec.

Import Bool ssreflect BinNat ListNotations.

(* Ltac does not survive a Section, and toplevel_correct.v needs this
   one too, so it is defined before the section opens. *)
Ltac wf_proj := cbn [s_funcs s_tables s_mems s_globals s_elems s_datas] in *.

Section Instantiation.

Context `{hfc : host_function_class} `{memory : BlockUpdateMemory} `{ho : host}.

(* ── 1. The store relation ────────────────────────────────────────
   Two funcinsts are related when they have the same type and instance
   and their bodies are related by [rel_bs] at some map.  The map is
   existential rather than [compute_phi ...] because the relation has
   to be stable under the store operations, which do not carry the
   module's type table around; alloc_correct supplies the witness at
   the one place a related store is built.

   The second conjunct of [code_rel] is the frame agreement a fresh
   activation needs.  It is not free: [r_invoke_native] builds
   [f_locs := vs ++ defaults] on both sides, and [R_phi_live] then asks
   that a live local and its slot hold equal values there.  Below the
   parameter count phi is the identity, so that is trivial; above it
   every local starts at its default, and [module_supported] forces
   every local to be i32, so all the defaults are the same value.  That
   is the argument [frames_agree_entry] discharges. *)

Definition code_rel (ts1 : list value_type) (code code_opt : module_func) : Prop :=
  modfunc_type code_opt = modfunc_type code /\
  modfunc_locals code_opt = modfunc_locals code /\
  exists phi,
    rel_bs phi (fun _ => False) (modfunc_body code) (modfunc_body code_opt) /\
    forall inst vs defaults (L : N -> Prop),
      length vs = length ts1 ->
      default_vals (modfunc_locals code) = Some defaults ->
      frames_agree phi L
        {| f_locs := seq.cat vs defaults; f_inst := inst |}
        {| f_locs := seq.cat vs defaults; f_inst := inst |}.

Definition funcinst_rel (fi fi_opt : funcinst) : Prop :=
  match fi with
  | FC_func_host tf h => fi_opt = FC_func_host tf h
  | FC_func_native (Tf ts1 ts2) inst code =>
      exists code_opt,
        fi_opt = FC_func_native (Tf ts1 ts2) inst code_opt /\
        code_rel ts1 code code_opt
  end.

(* Everything a program can observe is equal; only the code differs. *)
Definition store_rel (s s_opt : store_record) : Prop :=
  List.Forall2 funcinst_rel (s_funcs s) (s_funcs s_opt) /\
  store_visible_eq s s_opt.

Lemma store_rel_lookup : forall s s_opt a fi,
  store_rel s s_opt ->
  lookup_N (s_funcs s) a = Some fi ->
  exists fi_opt, lookup_N (s_funcs s_opt) a = Some fi_opt /\ funcinst_rel fi fi_opt.
Proof.
  intros s s_opt a fi [Hfs _] Hlk.
  exact (Forall2_nth_impl Hfs Hlk).
Qed.

Lemma store_rel_lookup_bwd : forall s s_opt a fi_opt,
  store_rel s s_opt ->
  lookup_N (s_funcs s_opt) a = Some fi_opt ->
  exists fi, lookup_N (s_funcs s) a = Some fi /\ funcinst_rel fi fi_opt.
Proof.
  intros s s_opt a fi_opt [Hfs _] Hlk.
  exact (Forall2_nth_impl' Hfs Hlk).
Qed.

(* [cl_type] is read by r_call_indirect and r_return_invoke, and the
   relation keeps it fixed. *)
Lemma funcinst_rel_type : forall fi fi_opt,
  funcinst_rel fi fi_opt -> cl_type fi_opt = cl_type fi.
Proof.
  intros fi fi_opt H.
  destruct fi as [tf inst code | tf h]; simpl in H.
  - destruct tf as [ts1 ts2].
    destruct H as [code_opt [Heq _]]. subst fi_opt. reflexivity.
  - subst fi_opt. reflexivity.
Qed.

(* [with_funcs s fs] is [s] carrying different code.  [store_rel] fixes
   every section but [s_funcs], so a related store always has this
   shape -- see [store_rel_shape] in toplevel_correct.v, which is where
   the simulation makes use of it. *)
Definition with_funcs (s : store_record) (fs : list funcinst) : store_record :=
  {| s_funcs := fs; s_tables := s_tables s; s_mems := s_mems s;
     s_globals := s_globals s; s_elems := s_elems s; s_datas := s_datas s |}.

(* Configuration projections.  [cfg_store] is in coalesce_locals_correct.v;
   these three are its cousins, and live here because both halves of the
   proof read them. *)
Definition cfg_frame
  (c : host_state * store_record * frame * list administrative_instruction)
  : frame := let '(_, _, f, _) := c in f.
(* ── 2. Typing preservation ───────────────────────────────────────
   [instantiate] carries [module_typing] as a conjunct, so the
   coalesced module has to validate.  The pass leaves [modfunc_type]
   and [modfunc_locals] alone, so the typing context is unchanged and
   the obligation is entirely about the body: a renamed local.get /
   local.set must have the same type as the original.  That holds
   because [module_supported] forces every local to be i32 and phi
   stays inside the declared slot range, so the renamed index has the
   same declared type. *)

Lemma map_apply_phi_cat : forall phi (l1 l2 : list basic_instruction),
  List.map (apply_phi phi) (seq.cat l1 l2)
  = seq.cat (List.map (apply_phi phi) l1) (List.map (apply_phi phi) l2).
Proof.
  intros phi l1 l2. induction l1 as [| a l IH]; simpl;
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* The whole of the local-index case: the original index resolves, so it
   is in range; phi keeps it in range; and every slot has the same type,
   so the renamed index resolves to the same one. *)
Lemma i32_lookup_phi : forall C phi x t,
  List.Forall (fun u => u = T_num T_i32) (tc_locals C) ->
  (forall i, N.to_nat i < length (tc_locals C) ->
             N.to_nat (apply_phi_local phi i) < length (tc_locals C)) ->
  lookup_N (tc_locals C) x = Some t ->
  lookup_N (tc_locals C) (apply_phi_local phi x) = Some t.
Proof.
  intros C phi x t Hi32 Hrange Hx.
  assert (Hlt : N.to_nat x < length (tc_locals C)).
  { apply nth_error_Some. unfold lookup_N in Hx. rewrite Hx. discriminate. }
  assert (Ht : t = T_num T_i32).
  { apply (proj1 (Forall_forall _ _) Hi32). eapply nth_error_In. exact Hx. }
  pose proof (Hrange x Hlt) as Hr.
  unfold lookup_N in *.
  destruct (nth_error (tc_locals C) (N.to_nat (apply_phi_local phi x)))
    as [u |] eqn:E.
  - f_equal. rewrite Ht.
    apply (proj1 (Forall_forall _ _) Hi32). eapply nth_error_In. exact E.
  - exfalso. apply nth_error_None in E. lia.
Qed.

Lemma be_typing_apply_phi : forall C phi bs tf,
  List.Forall (fun t => t = T_num T_i32) (tc_locals C) ->
  (forall i, N.to_nat i < length (tc_locals C) ->
             N.to_nat (apply_phi_local phi i) < length (tc_locals C)) ->
  be_typing C bs tf ->
  be_typing C (List.map (apply_phi phi) bs) tf.
Proof.
  intros C phi bs tf H1 H2 Hty. revert H1 H2.
  induction Hty; intros Hi32 Hrange; simpl.
  (* every instruction apply_phi leaves alone *)
  all: try (solve [ econstructor; eassumption ]).
  all: try (solve [ constructor; assumption ]).
  (* the structured instructions: upd_label does not touch tc_locals *)
  - apply bet_block; [exact H |].
    apply IHHty; unfold upd_label; cbn [tc_locals]; assumption.
  - apply bet_loop; [exact H |].
    apply IHHty; unfold upd_label; cbn [tc_locals]; assumption.
  - apply bet_if_wasm; [exact H | |];
      [ apply IHHty1 | apply IHHty2 ];
      unfold upd_label; cbn [tc_locals]; assumption.
  (* the three that phi actually rewrites *)
  - apply bet_local_get. apply i32_lookup_phi; assumption.
  - apply bet_local_set. apply i32_lookup_phi; assumption.
  - apply bet_local_tee. apply i32_lookup_phi; assumption.
  (* and the two structural rules *)
  - rewrite map_apply_phi_cat.
    eapply bet_composition;
      [apply IHHty1; assumption | apply IHHty2; assumption].
  - eapply bet_subtyping; [apply IHHty; assumption | exact H].
Qed.

(* modfunc_type and modfunc_locals survive the pass untouched, so the
   typing context is the same one and only the body has to be re-typed.
   The two side conditions be_typing_apply_phi wants are exactly what
   func_supported buys: every slot is i32, and phi stays inside the
   declared range (alloc_correct's compute_phi_range). *)
Lemma module_func_typing_coalesce : forall types C f tf,
  func_supported types f = true ->
  tc_types C = types ->
  module_func_typing C f tf ->
  module_func_typing C (coalesce_func_with_types types f) tf.
Proof.
  intros types C f tf Hs Hc Hty.
  destruct f as [x t_locs b_es]. destruct tf as [tn tm].
  destruct Hty as [Hlk [Hbe Hdef]].
  unfold coalesce_func_with_types, coalesce_func, apply_phi_func.
  cbn [modfunc_type modfunc_locals modfunc_body].
  split; [exact Hlk | split; [| exact Hdef]].
  subst types.
  assert (Hst : slot_types (tc_types C)
                  {| modfunc_type := x; modfunc_locals := t_locs;
                     modfunc_body := b_es |} = seq.cat tn t_locs).
  { unfold slot_types. cbn [modfunc_type modfunc_locals]. rewrite Hlk.
    reflexivity. }
  assert (Hn : func_total_locals (tc_types C)
                 {| modfunc_type := x; modfunc_locals := t_locs;
                    modfunc_body := b_es |}
               = N.of_nat (length (seq.cat tn t_locs))).
  { rewrite <- slot_types_length. rewrite Hst. reflexivity. }
  apply be_typing_apply_phi.
  - unfold upd_local_label_return. cbn [tc_locals].
    rewrite <- Hst. apply Forall_forall. intros t Ht.
    apply value_type_eqb_eq.
    exact (proj1 (forallb_forall _ _) (func_supported_i32 _ _ Hs) t Ht).
  - unfold upd_local_label_return. cbn [tc_locals]. intros i Hi.
    assert (Hlt : (i < func_total_locals (tc_types C)
                     {| modfunc_type := x; modfunc_locals := t_locs;
                        modfunc_body := b_es |})%N) by (rewrite Hn; lia).
    pose proof (compute_phi_range _ _ _ (T_num T_i32) b_es i
                  (func_supported_uniform _ _ Hs) Hlt) as Hr.
    cbn [modfunc_type] in Hr. lia.
  - exact Hbe.
Qed.

Lemma Forall2_module_func_typing_coalesce : forall types C fs fts,
  tc_types C = types ->
  Forall (fun f => func_supported types f = true) fs ->
  Forall2 (module_func_typing C) fs fts ->
  Forall2 (module_func_typing C) (map (coalesce_func_with_types types) fs) fts.
Proof.
  intros types C fs fts Hc Hall H.
  induction H as [| g tg gs' tgs' Hg Hrest IH]; simpl.
  - constructor.
  - inversion Hall; subst. constructor.
    + apply module_func_typing_coalesce; [exact H1 | reflexivity | exact Hg].
    + apply IH. exact H2.
Qed.

(* Only the function list changes, and module_filter_funcidx -- the one
   part of the typing context that is computed from the module -- reads
   globals, elems, datas and exports, never mod_funcs.  So the two
   contexts are the same context and every conjunct but the functions'
   is the hypothesis unchanged. *)
Lemma module_typing_coalesce : forall m impts expts,
  module_supported m = true ->
  module_typing m impts expts ->
  module_typing (coalesce_module m) impts expts.
Proof.
  intros m impts expts Hsup Hty.
  assert (Hall : Forall (fun g => func_supported (mod_types m) g = true)
                        (mod_funcs m)).
  { unfold module_supported in Hsup. destruct (mod_start m); [discriminate |].
    apply Forall_forall. intros x Hx.
    exact (proj1 (forallb_forall _ _) Hsup x Hx). }
  unfold coalesce_module. rewrite Hsup.
  destruct m as [tfs fs ts ms gs els ds i_opt imps exps]. simpl in Hall.
  destruct Hty as [fts [tts [mts [gts [rts [dts Hty]]]]]].
  exists fts, tts, mts, gts, rts, dts.
  unfold coalesce_module_supported. simpl.
  unfold module_filter_funcidx.
  cbn [mod_globals mod_elems mod_datas mod_exports].
  unfold module_filter_funcidx in Hty.
  cbn [mod_globals mod_elems mod_datas mod_exports] in Hty.
  cbv zeta in Hty.
  destruct Hty as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]]]]].
  repeat split; try assumption.
  eapply Forall2_module_func_typing_coalesce;
    [reflexivity | exact Hall | exact H2].
Qed.

(* ── 3. Instantiation preservation ────────────────────────────────
   Allocation walks [mod_funcs] and stores one funcinst per entry; the
   pass changes only [modfunc_body], so the addresses, the instance and
   every other store section come out identical, and the two function
   lists are pointwise [funcinst_rel] by construction --
   [frames_agree_entry] is what supplies the second half of
   [code_rel].

   The initializers need no work of their own: [mod_globals],
   [mod_elems] and [mod_datas] are copied verbatim, and
   [module_supported] rejects a module with a start function, so [bes]
   contains no call into coalesced code. *)

Lemma length_seq_map : forall (A B : Type) (g : A -> B) l,
  length (seq.map g l) = length l.
Proof.
  intros A B g l. induction l as [| a l' IH]; simpl;
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* Every local starts at its type's default, and every local is i32, so
   every non-parameter slot starts at the same value.  That is why a
   coalesced frame agrees with the original one at entry however the
   scan permuted the slots. *)
Lemma default_vals_i32_nth : forall ts ds k,
  List.Forall (fun t => t = T_num T_i32) ts ->
  default_vals ts = Some ds ->
  k < length ds ->
  nth_error ds k = Some (VAL_num (bitzero T_i32)).
Proof.
  intros ts ds k Hall Hd Hk. unfold default_vals in Hd.
  pose proof (those_length Hd) as Hlen. rewrite length_seq_map in Hlen.
  destruct (nth_error ts k) as [t |] eqn:E;
    [| apply nth_error_None in E; lia].
  assert (Ht : t = T_num T_i32)
    by (apply (proj1 (Forall_forall _ _) Hall); eapply nth_error_In; exact E).
  subst t.
  destruct (those_map_lookup Hd E) as [y [Hy Hny]].
  cbn in Hy. injection Hy as Hy. subst y. exact Hny.
Qed.

Lemma frames_agree_entry : forall types f vs defaults inst L,
  func_supported types f = true ->
  N.of_nat (length vs) = func_param_count types f.(modfunc_type) ->
  default_vals f.(modfunc_locals) = Some defaults ->
  frames_agree (compute_phi (slot_types types f)
                  (func_param_count types f.(modfunc_type))
                  (func_total_locals types f) f.(modfunc_body))
               L
               {| f_locs := seq.cat vs defaults; f_inst := inst |}
               {| f_locs := seq.cat vs defaults; f_inst := inst |}.
Proof.
  intros types f vs defaults inst L Hs Hvs Hd.
  assert (Hi32 : List.Forall (fun t => t = T_num T_i32) (modfunc_locals f)).
  { apply Forall_forall. intros x Hx. apply value_type_eqb_eq.
    apply (proj1 (forallb_forall _ _) (func_supported_i32 _ _ Hs) x).
    unfold slot_types. destruct (lookup_N types (modfunc_type f)) as [[ps rs] |].
    - apply in_or_app. right. exact Hx.
    - exact Hx. }
  assert (Hdl : length defaults = length (modfunc_locals f)).
  { unfold default_vals in Hd. pose proof (those_length Hd) as H.
    rewrite length_seq_map in H. lia. }
  assert (Hlen : N.of_nat (length (seq.cat vs defaults))
                 = func_total_locals types f).
  { unfold func_total_locals. rewrite <- Hvs.
    assert (Hcat : length (seq.cat vs defaults) = length vs + length defaults)
      by (rewrite <- length_app; reflexivity).
    rewrite Hcat. rewrite Hdl. lia. }
  cbn [f_locs f_inst].
  split; [reflexivity | split; [| split]].
  { cbn [f_locs]. intros i Hi.
    pose proof (compute_phi_range _ _ _ (T_num T_i32) (modfunc_body f) i
                  (func_supported_uniform _ _ Hs) ltac:(lia)) as Hr.
    lia. }
  { (* backwards: an index past the last local is not renamed, so its slot
       is itself and is out of range on the other side too *)
    cbn [f_locs]. intros i Hi.
    destruct (N.leb (func_total_locals types f) i) eqn:Ege.
    - apply N.leb_le in Ege.
      rewrite (compute_phi_id_above _ _ _ _ _ Ege) in Hi. lia.
    - apply N.leb_gt in Ege. lia. }
  { cbn [f_locs]. intros i Hi _.
    destruct (N.ltb i (func_param_count types (modfunc_type f))) eqn:Elt.
    - (* a parameter: phi is the identity there, so the two frames agree
         because they are the same frame *)
      apply N.ltb_lt in Elt.
      rewrite (compute_phi_id_below _ _ _ _ _ Elt). reflexivity.
    - (* a declared local: both it and its slot sit in the defaults, and
         every default is the same i32 zero *)
      apply N.ltb_ge in Elt.
      pose proof (compute_phi_lower _ _ _ (T_num T_i32) (modfunc_body f) i
                    (func_supported_uniform _ _ Hs) Elt ltac:(lia)) as Hlo.
      pose proof (compute_phi_range _ _ _ (T_num T_i32) (modfunc_body f) i
                    (func_supported_uniform _ _ Hs) ltac:(lia)) as Hhi.
      assert (Hcat : length (seq.cat vs defaults) = length vs + length defaults)
        by (rewrite <- length_app; reflexivity).
      assert (Hsplit : forall k, length vs <= k ->
                k < length (seq.cat vs defaults) ->
                nth_error (seq.cat vs defaults) k
                  = Some (VAL_num (bitzero T_i32))).
      { intros k Hk1 Hk2.
        assert (Heq : seq.cat vs defaults = vs ++ defaults) by reflexivity.
        rewrite Heq. rewrite nth_error_app2; [| exact Hk1].
        apply (default_vals_i32_nth (modfunc_locals f));
          [exact Hi32 | exact Hd | lia]. }
      rewrite Hsplit; [| lia | lia].
      rewrite Hsplit; [reflexivity | lia | lia]. }
Qed.

Lemma with_funcs_id : forall s, with_funcs s (s_funcs s) = s.
Proof. intros s. unfold with_funcs. destruct s. reflexivity. Qed.

(* ── Allocation ───────────────────────────────────────────────────
   alloc_module threads the store through six allocators.  Five of them
   append to one section and rebuild the record leaving s_funcs alone,
   so they commute with with_funcs; only alloc_funcs is interesting, and
   there the two runs start from the *same* store, so they hand out the
   same addresses. *)

Definition alloc_fold {A B} (g : store_record -> A -> store_record * B)
  : store_record * list B -> A -> store_record * list B :=
  fun '(s0, ys) (x : A) => let '(s', y) := g s0 x in (s', y :: ys).

Lemma alloc_Xs_fold : forall A B (g : store_record -> A -> store_record * B) s xs,
  alloc_Xs g s xs
  = (fst (fold_left (alloc_fold g) xs (s, [])),
     rev (snd (fold_left (alloc_fold g) xs (s, [])))).
Proof.
  intros A B g s xs. unfold alloc_Xs.
  change (fun '(s0, ys) (x : A) => let '(s', y) := g s0 x in (s', y :: ys))
    with (alloc_fold g).
  destruct (fold_left (alloc_fold g) xs (s, [])) as [s' fas]. reflexivity.
Qed.

Definition wf_commutes {A B} (g : store_record -> A -> store_record * B)
  (fs : list funcinst) : Prop :=
  forall s x, g (with_funcs s fs) x = (with_funcs (fst (g s x)) fs, snd (g s x)).

Lemma alloc_fold_with_funcs :
  forall A B (g : store_record -> A -> store_record * B) fs,
  wf_commutes g fs ->
  forall xs s ys,
    fold_left (alloc_fold g) xs (with_funcs s fs, ys)
    = (with_funcs (fst (fold_left (alloc_fold g) xs (s, ys))) fs,
       snd (fold_left (alloc_fold g) xs (s, ys))).
Proof.
  intros A B g fs Hg xs. induction xs as [| x xs IH]; intros s ys; simpl.
  - reflexivity.
  - unfold alloc_fold at 1 3. rewrite Hg.
    destruct (g s x) as [s1 y] eqn:Egx. cbn [fst snd].
    exact (IH s1 (y :: ys)).
Qed.

Lemma alloc_Xs_with_funcs :
  forall A B (g : store_record -> A -> store_record * B) fs,
  wf_commutes g fs ->
  forall xs s,
    alloc_Xs g (with_funcs s fs) xs
    = (with_funcs (fst (alloc_Xs g s xs)) fs, snd (alloc_Xs g s xs)).
Proof.
  intros A B g fs Hg xs s.
  rewrite ! alloc_Xs_fold. rewrite alloc_fold_with_funcs; [| exact Hg].
  cbn [fst snd]. reflexivity.
Qed.

Ltac alloc_commutes_solve :=
  intros ? ?;
  repeat match goal with
         | x : memory_type |- _ => destruct x
         | x : table_type |- _ => destruct x
         | x : limits |- _ => destruct x
         | x : _ * _ |- _ => destruct x
         end;
  cbv beta iota zeta delta
    [ with_funcs alloc_tab alloc_tab_ref alloc_mem alloc_glob alloc_elem
      alloc_data add_table add_mem add_glob add_elem add_data ];
  wf_proj; reflexivity.

(* An allocator that commutes with with_funcs at every fs in particular
   leaves s_funcs alone: take fs to be s_funcs s. *)
Lemma alloc_Xs_keeps_funcs :
  forall A B (g : store_record -> A -> store_record * B),
  (forall fs, wf_commutes g fs) ->
  forall xs s, s_funcs (fst (alloc_Xs g s xs)) = s_funcs s.
Proof.
  intros A B g Hg xs s.
  pose proof (alloc_Xs_with_funcs A B g (s_funcs s) (Hg _) xs s) as H.
  rewrite with_funcs_id in H.
  pose proof (f_equal (fun p => s_funcs (fst p)) H) as H2.
  cbn [fst] in H2. unfold with_funcs in H2. cbn [s_funcs] in H2. exact H2.
Qed.

Lemma alloc_tab_commutes : forall fs, wf_commutes alloc_tab fs.
Proof. intros fs. unfold wf_commutes. alloc_commutes_solve. Qed.

Lemma alloc_mem_commutes : forall fs, wf_commutes alloc_mem fs.
Proof. intros fs. unfold wf_commutes. alloc_commutes_solve. Qed.

Lemma alloc_glob_commutes : forall fs, wf_commutes alloc_glob fs.
Proof. intros fs. unfold wf_commutes. alloc_commutes_solve. Qed.

Lemma alloc_elem_commutes : forall fs, wf_commutes alloc_elem fs.
Proof. intros fs. unfold wf_commutes. alloc_commutes_solve. Qed.

Lemma alloc_data_commutes : forall fs, wf_commutes alloc_data fs.
Proof. intros fs. unfold wf_commutes. alloc_commutes_solve. Qed.

(* Every function of a supported module is related to its coalesced
   image, whether or not the walk accepted it.  Accepted: the map is
   compute_phi's and alloc_correct supplies rel_bs.  Rejected: the map
   is empty, the body comes back unchanged, and bs_guarded -- which
   func_supported checks -- relates it to itself. *)
Lemma coalesce_func_code_rel : forall types f ts1,
  func_supported types f = true ->
  N.of_nat (length ts1) = func_param_count types (modfunc_type f) ->
  code_rel ts1 f (coalesce_func_with_types types f).
Proof.
  intros types f ts1 Hs Hpc'.
  assert (Hpc : func_param_count types (modfunc_type f) = N.of_nat (length ts1))
    by (symmetry; exact Hpc').
  unfold coalesce_func_with_types, coalesce_func, apply_phi_func.
  split; [reflexivity | split; [reflexivity |]].
  cbn [modfunc_type modfunc_locals modfunc_body].
  destruct (coalescable (func_param_count types (modfunc_type f))
                        (func_total_locals types f) (modfunc_body f)) eqn:Hc.
  - exists (compute_phi (slot_types types f)
              (func_param_count types (modfunc_type f))
              (func_total_locals types f) (modfunc_body f)).
    split.
    + exact (coalesce_func_with_types_related types f Hs Hc).
    + intros inst vs defaults L Hlen Hd.
      apply (frames_agree_entry types f vs defaults inst L Hs); [| exact Hd].
      rewrite Hpc. rewrite Hlen. reflexivity.
  - exists empty. rewrite (compute_phi_rejected _ _ _ _ Hc).
    rewrite map_apply_phi_empty_id. split.
    + apply rel_bs_refl. exact (func_supported_guarded types f Hs).
    + intros inst vs defaults L Hlen Hd. apply frames_agree_empty_refl.
Qed.

(* A funcinst whose own body satisfies the nesting restriction is
   related to itself, at the identity map.  This is what covers the
   *imported* functions: they are the same on both sides, but the
   relation still has to hold of them, and relating a body to itself is
   exactly [rel_bs_refl].  It is the reason [store_guarded] appears as a
   premise all the way up -- the original [sim_step] carried it for the
   same reason. *)
Lemma funcinst_rel_refl : forall fi,
  (forall tf inst code, fi = FC_func_native tf inst code ->
     bs_guarded (modfunc_body code) = true) ->
  funcinst_rel fi fi.
Proof.
  intros fi Hg. destruct fi as [tf inst code | tf h]; [| reflexivity].
  destruct tf as [ts1 ts2]. exists code. split; [reflexivity |].
  split; [reflexivity | split; [reflexivity |]].
  exists empty. split.
  - apply rel_bs_refl. exact (Hg _ _ _ eq_refl).
  - intros inst' vs defaults L Hlen Hd. apply frames_agree_empty_refl.
Qed.

Lemma store_guarded_self_rel : forall s,
  store_guarded s -> List.Forall2 funcinst_rel (s_funcs s) (s_funcs s).
Proof.
  intros s Hg. apply Forall2_spec; [reflexivity |].
  intros n fi fi' H1 H2. rewrite H1 in H2. injection H2 as H2. subst fi'.
  apply funcinst_rel_refl. intros tf inst code Heq. subst fi.
  exact (Hg (N.of_nat n) tf inst code
           (ltac:(unfold lookup_N; rewrite Nnat.Nat2N.id; exact H1))).
Qed.

(* alloc_funcs appends one funcinst per module function and hands out
   consecutive addresses from the current length; neither depends on the
   bodies, so the two runs agree on the addresses and differ only in
   s_funcs. *)
Lemma length_cat : forall A (a b : list A),
  length (seq.cat a b) = length a + length b.
Proof. intros A a b. rewrite <- length_app. reflexivity. Qed.

Lemma alloc_funcs_store : forall inst fs s ys,
  fst (fold_left (alloc_fold (fun s0 f => alloc_func s0 f inst)) fs (s, ys))
  = with_funcs s (seq.cat (s_funcs s)
                    (List.map (fun f => gen_func_instance f inst) fs)).
Proof.
  intros inst fs. induction fs as [| f fs IH]; intros s ys; simpl.
  - unfold with_funcs. rewrite seq.cats0. destruct s. reflexivity.
  - unfold alloc_fold at 1. unfold alloc_func. cbn [fst snd].
    rewrite IH. unfold with_funcs, add_func. wf_proj.
    rewrite <- seq.catA. reflexivity.
Qed.

Lemma alloc_funcs_addrs : forall inst fs fs2 s s2 ys,
  length fs = length fs2 ->
  length (s_funcs s) = length (s_funcs s2) ->
  snd (fold_left (alloc_fold (fun s0 f => alloc_func s0 f inst)) fs (s, ys))
  = snd (fold_left (alloc_fold (fun s0 f => alloc_func s0 f inst)) fs2 (s2, ys)).
Proof.
  intros inst fs. induction fs as [| f fs IH];
    intros fs2 s s2 ys Hlen Hs; destruct fs2 as [| f2 fs2]; simpl in *;
    try discriminate Hlen.
  - reflexivity.
  - unfold alloc_fold at 1 2. unfold alloc_func. cbn [fst snd].
    rewrite Hs. apply IH; [lia |].
    unfold add_func. wf_proj. rewrite ! length_cat. cbn [length]. lia.
Qed.

(* The same five facts at the level alloc_module actually uses. *)
Lemma alloc_tabs_with_funcs : forall fs s ts,
  alloc_tabs (with_funcs s fs) ts
  = (with_funcs (fst (alloc_tabs s ts)) fs, snd (alloc_tabs s ts)).
Proof.
  intros. unfold alloc_tabs. apply alloc_Xs_with_funcs, alloc_tab_commutes.
Qed.

Lemma alloc_mems_with_funcs : forall fs s ms,
  alloc_mems (with_funcs s fs) ms
  = (with_funcs (fst (alloc_mems s ms)) fs, snd (alloc_mems s ms)).
Proof.
  intros. unfold alloc_mems. apply alloc_Xs_with_funcs, alloc_mem_commutes.
Qed.

Lemma alloc_globs_with_funcs : forall fs s gs vs,
  alloc_globs (with_funcs s fs) gs vs
  = (with_funcs (fst (alloc_globs s gs vs)) fs, snd (alloc_globs s gs vs)).
Proof.
  intros. unfold alloc_globs. apply alloc_Xs_with_funcs, alloc_glob_commutes.
Qed.

Lemma alloc_elems_with_funcs : forall fs s es rs,
  alloc_elems (with_funcs s fs) es rs
  = (with_funcs (fst (alloc_elems s es rs)) fs, snd (alloc_elems s es rs)).
Proof.
  intros. unfold alloc_elems. apply alloc_Xs_with_funcs, alloc_elem_commutes.
Qed.

Lemma alloc_datas_with_funcs : forall fs s ds,
  alloc_datas (with_funcs s fs) ds
  = (with_funcs (fst (alloc_datas s ds)) fs, snd (alloc_datas s ds)).
Proof.
  intros. unfold alloc_datas. apply alloc_Xs_with_funcs, alloc_data_commutes.
Qed.

Lemma alloc_tabs_keeps_funcs : forall s ts,
  s_funcs (fst (alloc_tabs s ts)) = s_funcs s.
Proof. intros. apply alloc_Xs_keeps_funcs, alloc_tab_commutes. Qed.

Lemma alloc_mems_keeps_funcs : forall s ms,
  s_funcs (fst (alloc_mems s ms)) = s_funcs s.
Proof. intros. apply alloc_Xs_keeps_funcs, alloc_mem_commutes. Qed.

Lemma alloc_globs_keeps_funcs : forall s gs vs,
  s_funcs (fst (alloc_globs s gs vs)) = s_funcs s.
Proof. intros. apply alloc_Xs_keeps_funcs, alloc_glob_commutes. Qed.

Lemma alloc_elems_keeps_funcs : forall s es rs,
  s_funcs (fst (alloc_elems s es rs)) = s_funcs s.
Proof. intros. apply alloc_Xs_keeps_funcs, alloc_elem_commutes. Qed.

Lemma alloc_datas_keeps_funcs : forall s ds,
  s_funcs (fst (alloc_datas s ds)) = s_funcs s.
Proof. intros. apply alloc_Xs_keeps_funcs, alloc_data_commutes. Qed.

Lemma gen_func_instance_rel : forall types inst f,
  inst_types inst = types ->
  func_supported types f = true ->
  funcinst_rel (gen_func_instance f inst)
               (gen_func_instance (coalesce_func_with_types types f) inst).
Proof.
  intros types inst f Hti Hs.
  unfold gen_func_instance.
  replace (modfunc_type (coalesce_func_with_types types f))
    with (modfunc_type f) by reflexivity.
  rewrite Hti.
  destruct (lookup_N types (modfunc_type f)) as [[ts1 ts2] |] eqn:Hlk;
    cbn [funcinst_rel];
    eexists; (split; [reflexivity |]).
  - apply (coalesce_func_code_rel types f ts1 Hs).
    unfold func_param_count. rewrite Hlk. reflexivity.
  - apply (coalesce_func_code_rel types f [] Hs).
    unfold func_param_count. rewrite Hlk. reflexivity.
Qed.

Lemma alloc_module_coalesce : forall s m v_imps g_inits r_inits s_end inst,
  module_supported m = true ->
  store_guarded s ->
  alloc_module s m v_imps g_inits r_inits (s_end, inst) ->
  exists s_end_opt,
    alloc_module s (coalesce_module m) v_imps g_inits r_inits (s_end_opt, inst) /\
    store_rel s_end s_end_opt.
Proof.
  intros s m v_imps gvs rvs s_end inst Hsup Hg Halloc.
  assert (Hall : Forall (fun f => func_supported (mod_types m) f = true)
                        (mod_funcs m)).
  { unfold module_supported in Hsup. destruct (mod_start m); [discriminate |].
    apply Forall_forall. intros y Hy.
    exact (proj1 (forallb_forall _ _) Hsup y Hy). }
  assert (Hti : inst_types inst = mod_types m).
  { unfold alloc_module in Halloc.
    destruct (alloc_funcs s (mod_funcs m) inst) as [s1 i_fs].
    destruct (alloc_tabs s1 (seq.map modtab_type (mod_tables m))) as [s2 i_ts].
    destruct (alloc_mems s2 (seq.map modmem_type (mod_mems m))) as [s3 i_ms].
    destruct (alloc_globs s3 (mod_globals m) gvs) as [s4 i_gs].
    destruct (alloc_elems s4 (mod_elems m) rvs) as [s5 i_es].
    destruct (alloc_datas s5 (mod_datas m)) as [s6 i_ds].
    exact (proj1 (proj2 Halloc)). }
  unfold coalesce_module. rewrite Hsup. unfold coalesce_module_supported.
  set (types := mod_types m) in *.
  set (FS := seq.cat (s_funcs s)
               (List.map (fun f => gen_func_instance f inst) (mod_funcs m))).
  set (FS' := seq.cat (s_funcs s)
                (List.map (fun f => gen_func_instance
                                      (coalesce_func_with_types types f) inst)
                          (mod_funcs m))).
  set (A := rev (snd (fold_left
                        (alloc_fold (fun s0 f => alloc_func s0 f inst))
                        (mod_funcs m) (s, [])))).
  (* the two runs of alloc_funcs start from the same store, so they hand
     out the same addresses and differ only in s_funcs *)
  assert (Efs : alloc_funcs s (mod_funcs m) inst = (with_funcs s FS, A)).
  { unfold alloc_funcs. rewrite alloc_Xs_fold. unfold A. f_equal.
    rewrite alloc_funcs_store. unfold FS. reflexivity. }
  assert (Efo : alloc_funcs s (List.map (coalesce_func_with_types types)
                                        (mod_funcs m)) inst
                = (with_funcs s FS', A)).
  { unfold alloc_funcs. rewrite alloc_Xs_fold. unfold A. f_equal.
    - rewrite alloc_funcs_store. unfold FS'. rewrite map_map. reflexivity.
    - f_equal.
      apply alloc_funcs_addrs; [ rewrite length_map; reflexivity | reflexivity ]. }
  unfold alloc_module in Halloc |- *.
  cbn [mod_types mod_funcs mod_tables mod_mems mod_globals mod_elems
       mod_datas mod_start mod_imports mod_exports] in *.
  rewrite Efo. rewrite Efs in Halloc.
  (* root the optimized chain at the same store the source chain uses *)
  replace (with_funcs s FS') with (with_funcs (with_funcs s FS) FS')
    by (unfold with_funcs; wf_proj; reflexivity).
  (* the other five allocators commute with with_funcs *)
  rewrite alloc_tabs_with_funcs.
  destruct (alloc_tabs (with_funcs s FS)
              (seq.map modtab_type (mod_tables m))) as [s2 i_ts] eqn:Et.
  cbn [fst snd].
  rewrite alloc_mems_with_funcs.
  destruct (alloc_mems s2 (seq.map modmem_type (mod_mems m))) as [s3 i_ms] eqn:Em.
  cbn [fst snd].
  rewrite alloc_globs_with_funcs.
  destruct (alloc_globs s3 (mod_globals m) gvs) as [s4 i_gs] eqn:Eg.
  cbn [fst snd].
  rewrite alloc_elems_with_funcs.
  destruct (alloc_elems s4 (mod_elems m) rvs) as [s5 i_es] eqn:Ee.
  cbn [fst snd].
  rewrite alloc_datas_with_funcs.
  destruct (alloc_datas s5 (mod_datas m)) as [s6 i_ds] eqn:Ed.
  cbn [fst snd].
  destruct Halloc as [Hs' Hrest]. subst s_end.
  exists (with_funcs s6 FS'). split.
  - split; [reflexivity | exact Hrest].
  - split.
    + (* the funcinst lists are related pointwise *)
      assert (Hkeep : s_funcs s6 = FS).
      { pose proof (alloc_datas_keeps_funcs s5 (mod_datas m)) as K6.
        pose proof (alloc_elems_keeps_funcs s4 (mod_elems m) rvs) as K5.
        pose proof (alloc_globs_keeps_funcs s3 (mod_globals m) gvs) as K4.
        pose proof (alloc_mems_keeps_funcs s2
                      (seq.map modmem_type (mod_mems m))) as K3.
        pose proof (alloc_tabs_keeps_funcs (with_funcs s FS)
                      (seq.map modtab_type (mod_tables m))) as K2.
        rewrite Ed in K6. rewrite Ee in K5. rewrite Eg in K4.
        rewrite Em in K3. rewrite Et in K2.
        cbn [fst] in K2. cbn [fst] in K3. cbn [fst] in K4.
        cbn [fst] in K5. cbn [fst] in K6.
        rewrite K6. rewrite K5. rewrite K4. rewrite K3. rewrite K2.
        unfold with_funcs. cbn [s_funcs]. reflexivity. }
      cbn [s_funcs]. rewrite Hkeep. unfold FS'.
      assert (Hcat : forall A (a b : list A), seq.cat a b = a ++ b)
        by reflexivity.
      rewrite ! Hcat. apply Forall2_app.
      * exact (store_guarded_self_rel s Hg).
      * clear - Hall Hti. induction (mod_funcs m) as [| f fs IH]; simpl.
        -- constructor.
        -- inversion Hall; subst. constructor.
           ++ exact (gen_func_instance_rel types inst f Hti ltac:(assumption)).
           ++ exact (IH ltac:(assumption)).
    + repeat split; reflexivity.
Qed.

(* The globals' and elements' initializer expressions are untouched by
   the pass, and they run against the freshly allocated store, whose
   visible part is the same on both sides. *)
(* ── The initializers ─────────────────────────────────────────────
   mod_globals and mod_elems are copied verbatim, but their initializer
   runs still have to be replayed against the optimized store, and *at*
   it: instantiate_globals asks for a reduce_trans whose two endpoints
   are the same store.  So sim_trans_store is not enough -- it hands
   back a store merely *related* to the source's.

   What settles it is that these expressions are constant.  A constant
   expression is a list of constants, null and function references, and
   global.get; the only rule that reads the store is r_global_get, and
   store_rel holds s_globals equal.  So the run replays verbatim, and
   changes no store. *)

Definition ai_constish (e : administrative_instruction) : bool :=
  match e with
  | AI_basic (BI_const_num _) | AI_basic (BI_const_vec _)
  | AI_basic (BI_ref_null _)  | AI_basic (BI_ref_func _)
  | AI_basic (BI_global_get _) => true
  | AI_ref _ | AI_ref_extern _ => true
  | _ => false
  end.

Definition es_constish (es : list administrative_instruction) : bool :=
  List.forallb ai_constish es.

Lemma const_expr_constish : forall C b,
  const_expr C b = true -> ai_constish (AI_basic b) = true.
Proof. intros C b H. destruct b; cbn in *; try discriminate H; reflexivity. Qed.

Lemma const_exprs_constish : forall C bes,
  is_true (const_exprs C bes) -> es_constish (to_e_list bes) = true.
Proof.
  intros C bes. induction bes as [| b bes IH]; intros H; [reflexivity |].
  unfold const_exprs in H. cbn [seq.all] in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  unfold es_constish, to_e_list. cbn [seq.map List.forallb].
  rewrite (const_expr_constish C b H1). cbn [andb].
  exact (IH H2).
Qed.

Lemma es_constish_cat : forall a b,
  es_constish (seq.cat a b) = es_constish a && es_constish b.
Proof. intros a b. unfold es_constish. rewrite <- forallb_app. reflexivity. Qed.

(* No reduce_simple rule fires on a list of constants: every one of them
   needs an operator, a label or a trap in the list. *)
Lemma reduce_simple_not_constish : forall es es',
  reduce_simple es es' -> es_constish es = true -> False.
Proof.
  intros es es' H Hc. induction H;
    repeat (rewrite es_constish_cat in Hc);
    cbn in Hc; try discriminate Hc.
  all: try (rewrite ! Bool.andb_false_r in Hc; discriminate Hc).
  destruct lh as [vs es'' | ]; cbn in H0; subst es;
    rewrite ! es_constish_cat in Hc; cbn in Hc;
    rewrite ! Bool.andb_false_r in Hc; discriminate Hc.
Qed.

Lemma ai_constish_v_to_e : forall v, ai_constish (v_to_e v) = true.
Proof.
  intros v. destruct v as [n | vv | r]; [reflexivity | reflexivity |].
  destruct r; reflexivity.
Qed.

Lemma sglob_val_globals : forall s s2 inst j,
  s_globals s2 = s_globals s -> sglob_val s2 inst j = sglob_val s inst j.
Proof.
  intros s s2 inst j H.
  unfold sglob_val, sglob, sglob_ind, option_bind, option_map.
  rewrite H. reflexivity.
Qed.

(* So a constant expression changes nothing, stays constant, and replays
   against any store with the same globals.  Only three rules survive the
   shape restriction: ref.func and global.get, neither of which writes,
   and r_label under a base context. *)
Lemma reduce_constish : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  es_constish es = true ->
  hs' = hs /\ s' = s /\ f' = f /\ es_constish es' = true /\
  (forall s2, s_globals s2 = s_globals s -> reduce hs s2 f es hs s2 f es').
Proof.
  intros hs s f es hs' s' f' es' Hred. induction Hred; intros Hc;
    repeat (rewrite es_constish_cat in Hc); cbn in Hc;
    try discriminate Hc;
    try (rewrite ! Bool.andb_false_r in Hc; discriminate Hc).
  { destruct (reduce_simple_not_constish _ _ H Hc). }
  { repeat split; try reflexivity. intros s2 _. apply r_ref_func. exact H. }
  { repeat split; try reflexivity.
    - cbn. rewrite ai_constish_v_to_e. reflexivity.
    - intros s2 Hgl. apply r_global_get.
      rewrite (sglob_val_globals s s2 (f_inst f) i Hgl). exact H. }
  destruct lh as [vs es'' | k' vs n' l lh' l1]; cbn in H, H0.
  { subst les les'. rewrite ! es_constish_cat in Hc.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hv Hc].
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hes Hr].
    destruct (IHHred Hes) as [Hhs [Hss [Hff [Hce Hstep]]]].
    subst hs' s' f'. repeat split.
    - rewrite ! es_constish_cat. rewrite Hv. rewrite Hce. rewrite Hr.
      reflexivity.
    - intros s2 Hgl. eapply r_label with (lh := LH_base vs es'');
        [ exact (Hstep s2 Hgl) | reflexivity | reflexivity ]. }
  { subst les. rewrite es_constish_cat in Hc. cbn in Hc.
    rewrite ! Bool.andb_false_r in Hc. discriminate Hc. }
Qed.

Definition cfg_hs
  (c : host_state * store_record * frame * list administrative_instruction)
  : host_state := let '(hs, _, _, _) := c in hs.

Definition cfg_es
  (c : host_state * store_record * frame * list administrative_instruction)
  : list administrative_instruction := let '(_, _, _, es) := c in es.

Lemma reduce_trans_constish : forall c c',
  reduce_trans c c' -> es_constish (cfg_es c) = true ->
  cfg_hs c' = cfg_hs c /\ cfg_store c' = cfg_store c
  /\ cfg_frame c' = cfg_frame c /\ es_constish (cfg_es c') = true
  /\ (forall s2, s_globals s2 = s_globals (cfg_store c) ->
        reduce_trans (cfg_hs c, s2, cfg_frame c, cfg_es c)
                     (cfg_hs c, s2, cfg_frame c, cfg_es c')).
Proof.
  intros c c' Hred.
  induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz]; intros Hc.
  - destruct x as [[[hs s] f] es]. destruct y as [[[hs' s'] f'] es'].
    simpl in *.
    destruct (reduce_constish _ _ _ _ _ _ _ _ Hstep Hc)
      as [H1 [H2 [H3 [H4 H5]]]].
    repeat split; try assumption.
    intros s2 Hgl. apply Relation_Operators.rt_step. simpl. exact (H5 s2 Hgl).
  - repeat split; try reflexivity.
    + exact Hc.
    + intros s2 _. apply Relation_Operators.rt_refl.
  - destruct (IHxy Hc) as [H1 [H2 [H3 [H4 H5]]]].
    destruct (IHyz H4) as [G1 [G2 [G3 [G4 G5]]]].
    repeat split.
    + rewrite G1. exact H1.
    + rewrite G2. exact H2.
    + rewrite G3. exact H3.
    + exact G4.
    + intros s2 Hgl.
      eapply Relation_Operators.rt_trans; [ exact (H5 s2 Hgl) |].
      rewrite <- H1. rewrite <- H3.
      apply G5. rewrite H2. exact Hgl.
Qed.

Lemma init_expr_transfer : forall hs s s2 f bes v,
  es_constish (to_e_list bes) = true ->
  s_globals s2 = s_globals s ->
  reduce_trans (hs, s, f, to_e_list bes) (hs, s, f, [$V v]) ->
  reduce_trans (hs, s2, f, to_e_list bes) (hs, s2, f, [$V v]).
Proof.
  intros hs s s2 f bes v Hc Hgl Hred.
  destruct (reduce_trans_constish _ _ Hred Hc) as [_ [_ [_ [_ Hstep]]]].
  exact (Hstep s2 Hgl).
Qed.

Lemma init_exprs_transfer : forall C hs s s2 f bess rs,
  s_globals s2 = s_globals s ->
  Forall (fun bes => is_true (const_exprs C bes)) bess ->
  Forall2 (fun bes r => reduce_trans (hs, s, f, to_e_list bes)
                                     (hs, s, f, [$V VAL_ref r])) bess rs ->
  Forall2 (fun bes r => reduce_trans (hs, s2, f, to_e_list bes)
                                     (hs, s2, f, [$V VAL_ref r])) bess rs.
Proof.
  intros C hs s s2 f bess rs Hgl Hc H. revert Hc.
  induction H as [| bes r bs rs' Hbr Hb IH]; intros Hc; constructor.
  - eapply init_expr_transfer;
      [ exact (const_exprs_constish C _ (Forall_inv Hc)) | exact Hgl
      | exact Hbr ].
  - exact (IH (Forall_inv_tail Hc)).
Qed.

Lemma instantiate_globals_coalesce :
  forall C f_init hs s_end s_end_opt m g_inits,
  module_supported m = true ->
  store_rel s_end s_end_opt ->
  Forall (fun g => is_true (const_exprs C (modglob_init g))) (mod_globals m) ->
  instantiate_globals f_init hs s_end m g_inits ->
  instantiate_globals f_init hs s_end_opt (coalesce_module m) g_inits.
Proof.
  intros C f_init hs s_end s_end_opt m g_inits Hsup Hrel Hconst Hg.
  destruct Hrel as [_ [_ [_ [Hgl _]]]].
  assert (Hmg : mod_globals (coalesce_module m) = mod_globals m)
    by (unfold coalesce_module; rewrite Hsup; reflexivity).
  unfold instantiate_globals in *. rewrite Hmg. clear Hmg.
  revert Hconst.
  induction Hg as [| g v gs vs Hgv Hrest IH]; intros Hconst; constructor.
  - eapply init_expr_transfer;
      [ exact (const_exprs_constish C _ (Forall_inv Hconst))
      | symmetry; exact Hgl | exact Hgv ].
  - exact (IH (Forall_inv_tail Hconst)).
Qed.

Lemma instantiate_elems_coalesce :
  forall C f_init hs s_end s_end_opt m r_inits,
  module_supported m = true ->
  store_rel s_end s_end_opt ->
  Forall (fun e => Forall (fun bes => is_true (const_exprs C bes))
                          (modelem_init e)) (mod_elems m) ->
  instantiate_elems f_init hs s_end m r_inits ->
  instantiate_elems f_init hs s_end_opt (coalesce_module m) r_inits.
Proof.
  intros C f_init hs s_end s_end_opt m r_inits Hsup Hrel Hconst He.
  destruct Hrel as [_ [_ [_ [Hgl _]]]].
  assert (Hme : mod_elems (coalesce_module m) = mod_elems m)
    by (unfold coalesce_module; rewrite Hsup; reflexivity).
  unfold instantiate_elems in *. rewrite Hme. clear Hme.
  revert Hconst.
  induction He as [| e rs es rss Her Hrest IH]; intros Hconst; constructor.
  - exact (init_exprs_transfer C hs s_end s_end_opt f_init _ _
             (eq_sym Hgl) (Forall_inv Hconst) Her).
  - exact (IH (Forall_inv_tail Hconst)).
Qed.

Lemma Forall2_left : forall A B (R : A -> B -> Prop) (P : A -> Prop) l1 l2,
  (forall a b, R a b -> P a) -> Forall2 R l1 l2 -> Forall P l1.
Proof.
  intros A B R P l1 l2 HR H. induction H; constructor;
    [ eapply HR; eassumption | assumption ].
Qed.

(* const_exprs is a conjunct of module_typing, for both the globals'
   initializers and the elements'. *)
Lemma module_typing_const_globals : forall m impts expts,
  module_typing m impts expts ->
  exists C,
    Forall (fun g => is_true (const_exprs C (modglob_init g))) (mod_globals m).
Proof.
  intros m impts expts Hty.
  destruct m as [tfs fs ts ms gs els ds i_opt imps exps].
  destruct Hty as [fts [tts [mts [gts [rts [dts Hty]]]]]].
  cbv zeta in Hty.
  destruct Hty as [_ [_ [_ [_ [_ [Hg _]]]]]].
  eexists. cbn [mod_globals].
  refine (Forall2_left _ _ _ _ _ _ _ Hg).
  intros a b Hab. destruct a as [tg' es]. cbn [modglob_init].
  exact (proj1 Hab).
Qed.

Lemma module_typing_const_elems : forall m impts expts,
  module_typing m impts expts ->
  exists C,
    Forall (fun e => Forall (fun bes => is_true (const_exprs C bes))
                            (modelem_init e)) (mod_elems m).
Proof.
  intros m impts expts Hty.
  destruct m as [tfs fs ts ms gs els ds i_opt imps exps].
  destruct Hty as [fts [tts [mts [gts [rts [dts Hty]]]]]].
  cbv zeta in Hty.
  destruct Hty as [_ [_ [_ [_ [_ [_ [He _]]]]]]].
  eexists. cbn [mod_elems].
  refine (Forall2_left _ _ _ _ _ _ _ He).
  intros a b Hab. destruct a as [t' inits emode]. cbn [modelem_init].
  refine (Forall_impl _ _ (proj1 (proj2 Hab))).
  intros x Hx. exact (proj1 Hx).
Qed.

Lemma coalesce_instantiate : forall s m v_imps s_end f bes,
  module_supported m = true ->
  store_guarded s ->
  instantiate s m v_imps (s_end, f, bes) ->
  exists s_end_opt,
    instantiate s (coalesce_module m) v_imps (s_end_opt, f, bes) /\
    store_rel s_end s_end_opt.
Proof.
  intros s m v_imps s_end f bes Hsup Hg Hinst.
  destruct Hinst as [t_imps_mod [t_imps [t_exps [hs' [inst [g_inits [r_inits
    [Hty [Hext [Hsub [Halloc [Hglob [Helem [Hf Hbes]]]]]]]]]]]]]].
  destruct (alloc_module_coalesce s m v_imps g_inits r_inits s_end inst
              Hsup Hg Halloc)
    as [s_end_opt [Halloc_opt Hstore]].
  exists s_end_opt. split; [| exact Hstore].
  exists t_imps_mod, t_imps, t_exps, hs', inst, g_inits, r_inits.
  (* the pass copies everything but mod_funcs, so the initializer
     expressions and the start section are literally the same lists *)
  assert (Hfields : mod_elems (coalesce_module m) = mod_elems m
                    /\ mod_datas (coalesce_module m) = mod_datas m
                    /\ mod_start (coalesce_module m) = mod_start m).
  { unfold coalesce_module. rewrite Hsup. simpl. repeat split. }
  destruct Hfields as [He [Hd Hst]].
  repeat split.
  - apply module_typing_coalesce; assumption.
  - exact Hext.
  - exact Hsub.
  - exact Halloc_opt.
  - destruct (module_typing_const_globals _ _ _ Hty) as [Cg HCg].
    eapply instantiate_globals_coalesce;
      [ exact Hsup | exact Hstore | exact HCg | exact Hglob ].
  - destruct (module_typing_const_elems _ _ _ Hty) as [Ce HCe].
    eapply instantiate_elems_coalesce;
      [ exact Hsup | exact Hstore | exact HCe | exact Helem ].
  - exact Hf.
  - rewrite He. rewrite Hd. rewrite Hst. exact Hbes.
Qed.

End Instantiation.
