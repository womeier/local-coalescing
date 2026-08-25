(** From [compute_phi] to [slot_free].

    coalesce_locals_correct.v proves the simulation over an *arbitrary*
    rename map [phi], subject to [slot_free phi L i] at every write: no
    local the continuation can still read shares a slot with the one
    being written.  That is the register-allocation side condition, and
    it is the one obligation the simulation does not discharge itself.

    This file discharges it for the map the pass actually computes.  The
    argument is in three parts, each independent of the next:

    1. [find_free_slot] returns a slot no live local holds.  It searches
       a bounded range and falls back to the local's own index when the
       search runs out, so this is a counting argument: at most one slot
       per live local is blocked, and there are strictly more slots in
       range than live locals.

    2. The linear scan gives overlapping intervals distinct slots.  This
       is the invariant that [active] holds every unexpired assignment.

    3. A local live at a program point has that point inside its
       interval, so two locals live at the same point overlap.  This is
       what connects the walk's positions to the relation's liveness.
*)

From Wasm Require Import datatypes datatypes_properties opsem.
From Stdlib Require Import List Lia NArith FMapFacts Permutation.
From Wasmopt Require Import coalesce_locals coalesce_locals_correct toplevel_spec.

Import Bool BinNat ListNotations.

(* ── 1. find_free_slot returns a free, in-range slot ──────────────── *)

Lemma slot_used_spec : forall s active,
  slot_used_by_active s active = true <-> In s (List.map fst active).
Proof.
  intros s active. unfold slot_used_by_active. split.
  - intros H. apply existsb_exists in H. destruct H as [[s' e] [Hin Heq]].
    apply N.eqb_eq in Heq. subst s'.
    exact (in_map fst active (s, e) Hin).
  - intros H. apply in_map_iff in H. destruct H as [[s' e] [Heq Hin]].
    simpl in Heq. subst s'.
    apply existsb_exists. exists (s, e). split; [exact Hin | apply N.eqb_refl].
Qed.

Lemma slot_unused_spec : forall s active,
  slot_used_by_active s active = false <-> ~ In s (List.map fst active).
Proof.
  intros s active. split.
  - intros H Hin. apply slot_used_spec in Hin. rewrite H in Hin. discriminate.
  - intros H. destruct (slot_used_by_active s active) eqn:E; [| reflexivity].
    exfalso. apply H. apply slot_used_spec. exact E.
Qed.

(* The search cannot run out.  [skipped] accumulates the slots it has
   already rejected: they are distinct, they are all held by [active],
   and they all lie below the slot under consideration.  So if the
   search were to exhaust its budget, [active] would have to hold at
   least [rem + length skipped] distinct slots, which the cardinality
   hypothesis forbids. *)
Lemma find_free_slot_aux_free : forall tys t active fb rem slot skipped,
  (forall k, slot <= k < slot + rem -> slot_type_ok tys t (N.of_nat k) = true) ->
  NoDup skipped ->
  (forall s, In s skipped -> In s (List.map fst active)) ->
  (forall s, In s skipped -> exists k, s = N.of_nat k /\ k < slot) ->
  length active < rem + length skipped ->
  exists k, slot <= k < slot + rem
         /\ find_free_slot_aux tys t active fb rem slot = N.of_nat k
         /\ slot_used_by_active (N.of_nat k) active = false.
Proof.
  intros tys t active fb rem.
  induction rem as [|r IH]; intros slot skipped Hty Hnd Hsub Hbelow Hcard.
  - exfalso.
    assert (Hle : length skipped <= length (List.map fst active))
      by (apply NoDup_incl_length; [exact Hnd | exact Hsub]).
    rewrite length_map in Hle. simpl in Hcard. lia.
  - cbn [find_free_slot_aux].
    destruct (slot_used_by_active (N.of_nat slot) active) eqn:Hused.
    + cbn [orb].
      destruct (IH (S slot) (N.of_nat slot :: skipped))
        as [k [Hk [Heq Hfree]]].
      * intros k Hk. apply Hty. lia.
      * constructor; [| exact Hnd].
        intros Hin. destruct (Hbelow _ Hin) as [k' [Heq' Hk']].
        apply Nat2N.inj in Heq'. lia.
      * intros s [Hs | Hs]; [ subst s; apply slot_used_spec; exact Hused
                            | apply Hsub; exact Hs ].
      * intros s [Hs | Hs].
        -- subst s. exists slot. split; [reflexivity | lia].
        -- destruct (Hbelow _ Hs) as [k' [? ?]]. exists k'. split; [assumption | lia].
      * simpl. lia.
      * exists k. split; [lia | split; [exact Heq | exact Hfree]].
    + assert (Hok : slot_type_ok tys t (N.of_nat slot) = true) by (apply Hty; lia).
      rewrite Hok. cbn [orb negb].
      exists slot. split; [lia | split; [reflexivity | exact Hused]].
Qed.

(* Uniform slot types.  [module_supported] checks exactly this: every
   slot of every function is i32.  It is what makes the search above
   type-blind, and hence what makes the counting argument sufficient. *)
Definition tys_uniform (tys : list value_type) (pc n : N) (t : value_type) : Prop :=
  forall sl, (pc <= sl)%N -> (sl < n)%N -> lookup_N tys sl = Some t.

Lemma value_type_eqb_refl : forall t, value_type_eqb t t = true.
Proof.
  intros t. unfold value_type_eqb.
  destruct (value_type_eq_dec t t) as [Heq | Hne];
    [ reflexivity | exfalso; apply Hne; reflexivity ].
Qed.

(* Nnat has no order-transfer lemmas, but lia's zify knows N.of_nat. *)
Lemma slot_range : forall pc n k,
  N.to_nat pc <= k -> k < N.to_nat n ->
  (pc <= N.of_nat k)%N /\ (N.of_nat k < n)%N.
Proof. intros pc n k H1 H2. lia. Qed.

Lemma find_free_slot_free : forall tys pc n idx active t,
  lookup_N tys idx = Some t ->
  tys_uniform tys pc n t ->
  length active < N.to_nat n - N.to_nat pc ->
  let s := find_free_slot tys pc n idx active in
  (pc <= s)%N /\ (s < n)%N /\ slot_used_by_active s active = false.
Proof.
  intros tys pc n idx active t Ht Huni Hcard. cbn zeta.
  unfold find_free_slot. rewrite Ht.
  destruct (find_free_slot_aux_free tys t active idx
              (N.to_nat (n - pc)) (N.to_nat pc) [])
    as [k [Hk [Heq Hfree]]].
  - intros k Hk. rewrite N2Nat.inj_sub in Hk.
    destruct (slot_range pc n k) as [Hlo Hhi]; [ lia | lia |].
    unfold slot_type_ok. rewrite (Huni _ Hlo Hhi). apply value_type_eqb_refl.
  - constructor.
  - intros s [].
  - intros s [].
  - simpl. rewrite N2Nat.inj_sub. lia.
  - rewrite Heq. rewrite N2Nat.inj_sub in Hk.
    destruct (slot_range pc n k) as [Hlo Hhi]; [ lia | lia |].
    split; [exact Hlo | split; [exact Hhi | exact Hfree]].
Qed.

(* ── 2. the linear scan gives overlapping intervals distinct slots ── *)

Module MF := FMapFacts.Facts M.

Definition iv_local (x : localidx * nat * nat) : N := let '(i, _, _) := x in i.
Definition iv_start (x : localidx * nat * nat) : nat := let '(_, s, _) := x in s.
Definition iv_end   (x : localidx * nat * nat) : nat := let '(_, _, e) := x in e.

(* What sort_by_def delivers.  Stated transitively rather than pairwise on
   adjacent elements: every use below needs "the head starts no later than
   anything after it", which is what the scan's expiry argument turns on. *)
Fixpoint starts_nondec (l : list (localidx * nat * nat)) : Prop :=
  match l with
  | [] => True
  | x :: rest => (forall y, In y rest -> iv_start x <= iv_start y) /\ starts_nondec rest
  end.

Lemma expire_length : forall p active,
  length (expire_active p active) <= length active.
Proof.
  intros p active. unfold expire_active.
  induction active as [| [s l] rest IH]; simpl; [lia |].
  destruct (Nat.leb p l); simpl; lia.
Qed.

Lemma expire_keeps : forall p sl e active,
  In (sl, e) active -> p <= e -> In (sl, e) (expire_active p active).
Proof.
  intros p sl e active Hin Hle. unfold expire_active. apply filter_In.
  split; [exact Hin |]. cbn. apply PeanoNat.Nat.leb_le. exact Hle.
Qed.

(* A local the scan never looks at keeps whatever binding it had. *)
Lemma scan_preserves : forall tys pc n ivs active phi k,
  ~ In k (List.map iv_local ivs) ->
  M.find k (linear_scan_loop tys pc n ivs active phi) = M.find k phi.
Proof.
  intros tys pc n ivs. induction ivs as [| [[i si] ei] rest IH];
    intros active phi k Hk; cbn [linear_scan_loop]; [reflexivity |].
  rewrite IH.
  - apply MF.add_neq_o. intros Heq. apply Hk. left. exact Heq.
  - intros Hin. apply Hk. right. exact Hin.
Qed.

Lemma scan_keeps_some : forall tys pc n ivs active phi k sl,
  M.find k phi = Some sl ->
  exists sl', M.find k (linear_scan_loop tys pc n ivs active phi) = Some sl'.
Proof.
  intros tys pc n ivs. induction ivs as [| [[i si] ei] rest IH];
    intros active phi k sl H; cbn [linear_scan_loop].
  - exists sl. exact H.
  - destruct (N.eq_dec i k) as [He | Hne].
    + eapply IH. apply MF.add_eq_o. exact He.
    + eapply IH. rewrite MF.add_neq_o; [exact H | exact Hne].
Qed.

(* The heart of it.  An entry [(sl, e)] in [active] blocks its slot for
   every interval that starts at or before [e]: the expiry filter cannot
   drop it while the positions being processed are still <= e, and
   find_free_slot never returns a slot active holds. *)
Lemma scan_avoid : forall tys pc n t ivs,
  tys_uniform tys pc n t ->
  (forall x, In x ivs -> (pc <= iv_local x)%N /\ (iv_local x < n)%N) ->
  starts_nondec ivs ->
  NoDup (List.map iv_local ivs) ->
  forall active phi sl e,
  length active + length ivs <= N.to_nat n - N.to_nat pc ->
  In (sl, e) active ->
  forall k sk ek, In (k, sk, ek) ivs -> sk <= e ->
    exists slk, M.find k (linear_scan_loop tys pc n ivs active phi) = Some slk
             /\ slk <> sl.
Proof.
  intros tys pc n t ivs Huni.
  induction ivs as [| [[i si] ei] rest IH];
    intros Hrange Hsort Hdup active phi sl e Hcard Hactive k sk ek Hk Hle.
  - destruct Hk.
  - cbn [linear_scan_loop].
    destruct Hsort as [Hhd Hsort'].
    assert (Hsi : si <= e).
    { destruct Hk as [Heq | Hin].
      - injection Heq as H1 H2 H3. subst. exact Hle.
      - specialize (Hhd _ Hin). cbn in Hhd. lia. }
    assert (Hact' : In (sl, e) (expire_active si active))
      by (apply expire_keeps; assumption).
    assert (Hlen : length (expire_active si active) <= length active)
      by apply expire_length.
    assert (Hlt : length (expire_active si active) < N.to_nat n - N.to_nat pc)
      by (cbn in Hcard; lia).
    assert (Hty : lookup_N tys i = Some t).
    { destruct (Hrange (i, si, ei) (or_introl eq_refl)) as [Hlo Hhi].
      cbn in Hlo, Hhi. apply Huni; assumption. }
    destruct (find_free_slot_free tys pc n i (expire_active si active) t
                Hty Huni Hlt) as [_ [_ Hunused]].
    cbn zeta in Hunused.
    assert (Hne : find_free_slot tys pc n i (expire_active si active) <> sl).
    { intros Heq. apply slot_unused_spec in Hunused. apply Hunused.
      rewrite Heq. exact (in_map fst _ (sl, e) Hact'). }
    inversion Hdup as [| hd tl Hnotin Hdup' Heqd]; subst.
    destruct Hk as [Heq | Hin].
    + injection Heq as H1 H2 H3. subst k sk ek.
      eexists. split; [| exact Hne].
      rewrite scan_preserves; [| exact Hnotin].
      apply MF.add_eq_o. reflexivity.
    + assert (Hcard' :
        length ((find_free_slot tys pc n i (expire_active si active), ei)
                  :: expire_active si active) + length rest
        <= N.to_nat n - N.to_nat pc) by (cbn in Hcard |- *; lia).
      exact (IH (fun x Hx => Hrange x (or_intror Hx)) Hsort' Hdup'
                _ (M.add i (find_free_slot tys pc n i (expire_active si active)) phi)
                sl e Hcard' (or_intror Hact') k sk ek Hin Hle).
Qed.

(* Two locals whose intervals overlap get different slots. *)
Lemma scan_pair : forall tys pc n t ivs,
  tys_uniform tys pc n t ->
  (forall x, In x ivs -> (pc <= iv_local x)%N /\ (iv_local x < n)%N) ->
  starts_nondec ivs ->
  NoDup (List.map iv_local ivs) ->
  forall active phi,
  length active + length ivs <= N.to_nat n - N.to_nat pc ->
  forall i si ei j sj ej,
    In (i, si, ei) ivs -> In (j, sj, ej) ivs -> i <> j ->
    si <= ej -> sj <= ei ->
    exists sli slj,
      M.find i (linear_scan_loop tys pc n ivs active phi) = Some sli /\
      M.find j (linear_scan_loop tys pc n ivs active phi) = Some slj /\
      sli <> slj.
Proof.
  intros tys pc n t ivs Huni.
  induction ivs as [| [[h sh] eh] rest IH];
    intros Hrange Hsort Hdup active phi Hcard i si ei j sj ej Hi Hj Hij Hije Hjie.
  - destruct Hi.
  - cbn [linear_scan_loop].
    destruct Hsort as [Hhd Hsort'].
    inversion Hdup as [| hd tl Hnotin Hdup' Heqd]; subst.
    assert (Hlen : length (expire_active sh active) <= length active)
      by apply expire_length.
    assert (Hlt : length (expire_active sh active) < N.to_nat n - N.to_nat pc)
      by (cbn in Hcard; lia).
    assert (Hty : lookup_N tys h = Some t).
    { destruct (Hrange (h, sh, eh) (or_introl eq_refl)) as [Hlo Hhi].
      cbn in Hlo, Hhi. apply Huni; assumption. }
    destruct (find_free_slot_free tys pc n h (expire_active sh active) t
                Hty Huni Hlt) as [_ [_ Hunused]].
    cbn zeta in Hunused.
    set (slh := find_free_slot tys pc n h (expire_active sh active)) in *.
    set (act' := (slh, eh) :: expire_active sh active) in *.
    set (phi' := M.add h slh phi) in *.
    assert (Hcard' : length act' + length rest <= N.to_nat n - N.to_nat pc)
      by (unfold act'; cbn in Hcard |- *; lia).
    (* the head is i, the head is j, or neither *)
    destruct Hi as [Hi | Hi].
    + injection Hi as H1 H2 H3. subst h sh eh.
      assert (Hjr : In (j, sj, ej) rest)
        by (destruct Hj as [Hj | Hj]; [ injection Hj as -> -> ->; contradiction | exact Hj ]).
      destruct (scan_avoid tys pc n t rest Huni
                  (fun x Hx => Hrange x (or_intror Hx)) Hsort' Hdup'
                  act' phi' slh ei Hcard' (or_introl eq_refl) j sj ej Hjr Hjie)
        as [slj [Hfj Hnej]].
      exists slh, slj. split; [| split; [exact Hfj |]].
      * rewrite scan_preserves; [| exact Hnotin].
        apply MF.add_eq_o. reflexivity.
      * intros Heq. apply Hnej. symmetry. exact Heq.
    + destruct Hj as [Hj | Hj].
      * injection Hj as H1 H2 H3. subst h sh eh.
        destruct (scan_avoid tys pc n t rest Huni
                    (fun x Hx => Hrange x (or_intror Hx)) Hsort' Hdup'
                    act' phi' slh ej Hcard' (or_introl eq_refl) i si ei Hi Hije)
          as [sli [Hfi Hnei]].
        exists sli, slh. split; [exact Hfi | split; [| exact Hnei]].
        rewrite scan_preserves; [| exact Hnotin].
        apply MF.add_eq_o. reflexivity.
      * apply (IH (fun x Hx => Hrange x (or_intror Hx)) Hsort' Hdup'
                  act' phi' Hcard' i si ei j sj ej Hi Hj Hij Hije Hjie).
Qed.

(* sort_by_def is an insertion sort: it permutes, and it delivers the
   nondecreasing starts the scan's expiry argument needs. *)

Lemma insert_by_def_perm : forall x ys, Permutation (insert_by_def x ys) (x :: ys).
Proof.
  intros [[xi xst] xe] ys.
  induction ys as [| [[yi yst] ye] rest IH]; cbn [insert_by_def].
  - apply Permutation_refl.
  - destruct (Nat.leb xst yst).
    + apply Permutation_refl.
    + eapply Permutation_trans; [ apply perm_skip; exact IH | apply perm_swap ].
Qed.

Lemma sort_by_def_perm : forall l, Permutation (sort_by_def l) l.
Proof.
  induction l as [| x rest IH]; cbn [sort_by_def].
  - apply Permutation_refl.
  - eapply Permutation_trans;
      [ apply insert_by_def_perm | apply perm_skip; exact IH ].
Qed.

Lemma insert_by_def_nondec : forall x ys,
  starts_nondec ys -> starts_nondec (insert_by_def x ys).
Proof.
  intros [[xi xst] xe] ys.
  induction ys as [| [[yi yst] ye] rest IH]; intros H; cbn [insert_by_def].
  - split; [ intros y [] | exact I ].
  - destruct (Nat.leb xst yst) eqn:E.
    + split; [| exact H].
      intros y Hy. destruct Hy as [Hy | Hy].
      * subst y. cbn. apply PeanoNat.Nat.leb_le. exact E.
      * destruct H as [Hhd _]. specialize (Hhd _ Hy). cbn in Hhd |- *.
        apply PeanoNat.Nat.leb_le in E. lia.
    + destruct H as [Hhd Hrest]. split; [| apply IH; exact Hrest].
      intros y Hy.
      apply (Permutation_in _ (insert_by_def_perm (xi, xst, xe) rest)) in Hy.
      destruct Hy as [Hy | Hy].
      * subst y. cbn. apply PeanoNat.Nat.leb_gt in E. lia.
      * exact (Hhd _ Hy).
Qed.

Lemma sort_by_def_nondec : forall l, starts_nondec (sort_by_def l).
Proof.
  induction l as [| x rest IH]; cbn [sort_by_def];
    [ exact I | apply insert_by_def_nondec; exact IH ].
Qed.

(* Part 2, packaged: overlapping intervals get different slots, stated
   through apply_phi_local, which is how the relation reads phi. *)
Theorem linear_scan_disjoint : forall tys pc n t ivs i si ei j sj ej,
  tys_uniform tys pc n t ->
  (forall x, In x ivs -> (pc <= iv_local x)%N /\ (iv_local x < n)%N) ->
  NoDup (List.map iv_local ivs) ->
  length ivs <= N.to_nat n - N.to_nat pc ->
  In (i, si, ei) ivs -> In (j, sj, ej) ivs -> i <> j ->
  si <= ej -> sj <= ei ->
  apply_phi_local (linear_scan tys pc n ivs) i
    <> apply_phi_local (linear_scan tys pc n ivs) j.
Proof.
  intros tys pc n t ivs i si ei j sj ej Huni Hrange Hdup Hlen Hi Hj Hij Hije Hjie.
  assert (Hperm : Permutation (sort_by_def ivs) ivs) by apply sort_by_def_perm.
  destruct (scan_pair tys pc n t (sort_by_def ivs) Huni
              (fun x Hx => Hrange x (Permutation_in _ Hperm Hx))
              (sort_by_def_nondec ivs)
              (Permutation_NoDup (Permutation_map iv_local (Permutation_sym Hperm)) Hdup)
              [] empty
              ltac:(cbn; rewrite (Permutation_length Hperm); exact Hlen)
              i si ei j sj ej
              (Permutation_in _ (Permutation_sym Hperm) Hi)
              (Permutation_in _ (Permutation_sym Hperm) Hj)
              Hij Hije Hjie)
    as [sli [slj [Hfi [Hfj Hne]]]].
  unfold linear_scan, apply_phi_local. rewrite Hfi, Hfj. exact Hne.
Qed.

(* ── 3. a local live at a point has that point in its interval ────── *)

(* The walk over a list, named.  walk_instr builds this inline as a local
   [let], so the equations below hold by reflexivity. *)
Definition walk_bs (pc n : N) (d : nat) (st : walk_state)
  (bs : list basic_instruction) : walk_state :=
  List.fold_left (fun a i => walk_instr pc n d a i) bs st.

Definition ws_bump (st : walk_state) : walk_state :=
  mk_ws (ws_pos st + 1) (ws_defs st) (ws_uses st) (ws_ok st).

Definition ws_guard (b : list basic_instruction) (st : walk_state) : walk_state :=
  if body_ok_b b then st
  else mk_ws (ws_pos st) (ws_defs st) (ws_uses st) false.

Lemma walk_bs_nil : forall pc n d st, walk_bs pc n d st [] = st.
Proof. reflexivity. Qed.

Lemma walk_bs_cons : forall pc n d st b bs,
  walk_bs pc n d st (b :: bs) = walk_bs pc n d (walk_instr pc n d st b) bs.
Proof. reflexivity. Qed.

Lemma walk_block_eq : forall pc n d st bt b,
  walk_instr pc n d st (BI_block bt b)
    = walk_bs pc n (S d) (ws_guard b (ws_bump st)) b.
Proof. reflexivity. Qed.

Lemma walk_loop_eq : forall pc n d st bt b,
  walk_instr pc n d st (BI_loop bt b)
    = walk_bs pc n (S d) (ws_guard b (ws_bump st)) b.
Proof. reflexivity. Qed.

Lemma walk_if_eq : forall pc n d st bt b1 b2,
  walk_instr pc n d st (BI_if bt b1 b2)
    = walk_bs pc n (S d)
        (walk_bs pc n (S d) (ws_guard b2 (ws_guard b1 (ws_bump st))) b1) b2.
Proof. reflexivity. Qed.

(* A size measure that mirrors the walk's position counting. *)
Fixpoint bi_size (b : basic_instruction) {struct b} : nat :=
  let fix bss (bs : list basic_instruction) : nat :=
    match bs with
    | [] => 0
    | x :: r => bi_size x + bss r
    end in
  1 + match b with
      | BI_block _ bs => bss bs
      | BI_loop _ bs => bss bs
      | BI_if _ b1 b2 => bss b1 + bss b2
      | _ => 0
      end.

Fixpoint bs_size (bs : list basic_instruction) : nat :=
  match bs with
  | [] => 0
  | x :: r => bi_size x + bs_size r
  end.

(* The inner fix and bs_size are convertible: same body, and the
   recursive call unfolds to the same term. *)
Lemma bi_size_block : forall bt bs, bi_size (BI_block bt bs) = 1 + bs_size bs.
Proof. reflexivity. Qed.

Lemma bi_size_loop : forall bt bs, bi_size (BI_loop bt bs) = 1 + bs_size bs.
Proof. reflexivity. Qed.

(* Routed through BI_block so the two occurrences of the inner fix, which
   has no name outside the definition, cancel. *)
Lemma bi_size_if_block : forall bt b1 b2,
  bi_size (BI_if bt b1 b2)
    = bi_size (BI_block bt b1) + bi_size (BI_block bt b2) - 1.
Proof. intros bt b1 b2. cbn [bi_size]. lia. Qed.

Lemma bi_size_if : forall bt b1 b2,
  bi_size (BI_if bt b1 b2) = 1 + bs_size b1 + bs_size b2.
Proof.
  intros bt b1 b2. rewrite bi_size_if_block, !bi_size_block. lia.
Qed.

Lemma bi_size_pos : forall b, 1 <= bi_size b.
Proof. intros b. destruct b; cbn [bi_size]; lia. Qed.

(* Two facts about the walk, proved together because the second needs the
   first: a use recorded earlier is at a position below the current one,
   which is what makes overwriting it an increase.

   ws_wf: every def is a coalescable slot, recorded at or before the
   current position; every use is recorded strictly before it.
   ws_le: the walk only extends.  Defs are never rewritten -- def_instr
   keeps the first one -- uses only move forward, and ws_ok only falls. *)
Definition ws_wf (pc n : N) (st : walk_state) : Prop :=
  (forall k d, M.find k (ws_defs st) = Some d ->
     (pc <= k)%N /\ (k < n)%N /\ d <= ws_pos st)
  /\ (forall k u, M.find k (ws_uses st) = Some u -> u < ws_pos st).

Definition ws_le (st st' : walk_state) : Prop :=
  ws_pos st <= ws_pos st'
  /\ (forall k d, M.find k (ws_defs st) = Some d -> M.find k (ws_defs st') = Some d)
  /\ (forall k u, M.find k (ws_uses st) = Some u ->
        exists u', M.find k (ws_uses st') = Some u' /\ u <= u')
  /\ (ws_ok st' = true -> ws_ok st = true).

Lemma find_add_same : forall (A : Type) (m : M.t A) k (v : A),
  M.find k (M.add k v m) = Some v.
Proof. intros A m k v. apply MF.add_eq_o. reflexivity. Qed.

Lemma find_add_other : forall (A : Type) (m : M.t A) k k' (v : A),
  k <> k' -> M.find k' (M.add k v m) = M.find k' m.
Proof. intros A m k k' v H. apply MF.add_neq_o. exact H. Qed.

Lemma ws_le_refl : forall st, ws_le st st.
Proof.
  intros st. repeat split.
  - lia.
  - intros k d H. exact H.
  - intros k u H. exists u. split; [exact H | lia].
  - intros H. exact H.
Qed.

Lemma ws_le_trans : forall a b c, ws_le a b -> ws_le b c -> ws_le a c.
Proof.
  intros a b c [Hp1 [Hd1 [Hu1 Ho1]]] [Hp2 [Hd2 [Hu2 Ho2]]].
  repeat split.
  - lia.
  - intros k d H. apply Hd2. apply Hd1. exact H.
  - intros k u H. destruct (Hu1 _ _ H) as [u1 [H1 Hle1]].
    destruct (Hu2 _ _ H1) as [u2 [H2 Hle2]]. exists u2. split; [exact H2 | lia].
  - intros H. apply Ho1. apply Ho2. exact H.
Qed.

Lemma ws_bump_wf : forall pc n st, ws_wf pc n st -> ws_wf pc n (ws_bump st).
Proof.
  intros pc n st [Hd Hu]. split; cbn [ws_bump ws_pos ws_defs ws_uses].
  - intros k d H. destruct (Hd _ _ H) as [H1 [H2 H3]]. repeat split; [exact H1 | exact H2 | lia].
  - intros k u H. specialize (Hu _ _ H). lia.
Qed.

Lemma ws_bump_le : forall st, ws_le st (ws_bump st).
Proof.
  intros st. repeat split; cbn [ws_bump ws_pos ws_defs ws_uses ws_ok];
    try (intros; assumption); [ lia |].
  intros k u H. exists u. split; [exact H | lia].
Qed.

Lemma ws_guard_wf : forall pc n b st, ws_wf pc n st -> ws_wf pc n (ws_guard b st).
Proof.
  intros pc n b st H. unfold ws_guard. destruct (body_ok_b b); [exact H |].
  destruct H as [Hd Hu]. split; cbn; assumption.
Qed.

Lemma ws_guard_le : forall b st, ws_le st (ws_guard b st).
Proof.
  intros b st. unfold ws_guard. destruct (body_ok_b b); [apply ws_le_refl |].
  repeat split; cbn; try (intros; assumption).
  - lia.
  - intros k u H. exists u. split; [exact H | lia].
  - intros H. discriminate H.
Qed.

(* The read step, named.  A read of an undefined local is the
   use-before-def rejection: the use is not even recorded. *)
Definition ws_get (pc n : N) (st : walk_state) (idx : N) : walk_state :=
  if N.ltb idx pc then ws_bump st
  else if N.ltb idx n then
    if M.mem idx (ws_defs st)
    then mk_ws (ws_pos st + 1) (ws_defs st)
               (M.add idx (ws_pos st) (ws_uses st)) (ws_ok st)
    else mk_ws (ws_pos st + 1) (ws_defs st) (ws_uses st) false
  else ws_bump st.

Lemma walk_get_eq : forall pc n d st idx,
  walk_instr pc n d st (BI_local_get idx) = ws_get pc n st idx.
Proof. reflexivity. Qed.

Lemma ws_get_wf_le : forall pc n st idx,
  ws_wf pc n st ->
  ws_wf pc n (ws_get pc n st idx) /\ ws_le st (ws_get pc n st idx).
Proof.
  intros pc n st idx Hwf. unfold ws_get.
  destruct (N.ltb idx pc);
    [ split; [ apply ws_bump_wf; exact Hwf | apply ws_bump_le ] |].
  destruct (N.ltb idx n);
    [| split; [ apply ws_bump_wf; exact Hwf | apply ws_bump_le ]].
  destruct Hwf as [Hd Hu].
  destruct (M.mem idx (ws_defs st)).
  - split.
    + split; cbn [ws_pos ws_defs ws_uses].
      * intros k dd H. destruct (Hd _ _ H) as [? [? ?]].
        repeat split; [assumption | assumption | lia].
      * intros k u H. destruct (N.eq_dec idx k) as [He | Hne].
        -- subst k. rewrite find_add_same in H. injection H as <-. lia.
        -- rewrite find_add_other in H; [| exact Hne].
           specialize (Hu _ _ H). lia.
    + repeat split; cbn [ws_pos ws_defs ws_uses ws_ok].
      * lia.
      * intros k dd H. exact H.
      * intros k u H. destruct (N.eq_dec idx k) as [He | Hne].
        -- subst k. exists (ws_pos st). rewrite find_add_same.
           split; [reflexivity |]. specialize (Hu _ _ H). lia.
        -- exists u. rewrite find_add_other; [| exact Hne]. split; [exact H | lia].
      * intros H. exact H.
  - split.
    + split; cbn [ws_pos ws_defs ws_uses].
      * intros k dd H. destruct (Hd _ _ H) as [? [? ?]].
        repeat split; [assumption | assumption | lia].
      * intros k u H. specialize (Hu _ _ H). lia.
    + repeat split; cbn [ws_pos ws_defs ws_uses ws_ok].
      * lia.
      * intros k dd H. exact H.
      * intros k u H. exists u. split; [exact H | lia].
      * intros H. discriminate H.
Qed.

(* local.set and local.tee take the same step: def_instr. *)
Definition ws_def (pc n : N) (d : nat) (st : walk_state) (idx : N) : walk_state :=
  if N.ltb idx pc then ws_bump st
  else if N.ltb idx n then
    mk_ws (ws_pos st + 1)
          (M.add idx (match M.find idx (ws_defs st) with
                      | Some dd => dd
                      | None => if Nat.eqb d 0 then ws_pos st else 0
                      end) (ws_defs st))
          (M.add idx (ws_pos st) (ws_uses st))
          (ws_ok st)
  else ws_bump st.

Lemma walk_set_eq : forall pc n d st idx,
  walk_instr pc n d st (BI_local_set idx) = ws_def pc n d st idx.
Proof. reflexivity. Qed.

Lemma walk_tee_eq : forall pc n d st idx,
  walk_instr pc n d st (BI_local_tee idx) = ws_def pc n d st idx.
Proof. reflexivity. Qed.

Lemma ws_def_wf_le : forall pc n d st idx,
  ws_wf pc n st ->
  ws_wf pc n (ws_def pc n d st idx) /\ ws_le st (ws_def pc n d st idx).
Proof.
  intros pc n d st idx Hwf. unfold ws_def.
  destruct (N.ltb idx pc) eqn:E1;
    [ split; [ apply ws_bump_wf; exact Hwf | apply ws_bump_le ] |].
  destruct (N.ltb idx n) eqn:E2;
    [| split; [ apply ws_bump_wf; exact Hwf | apply ws_bump_le ]].
  apply N.ltb_ge in E1. apply N.ltb_lt in E2.
  destruct Hwf as [Hd Hu]. split.
  - split; cbn [ws_pos ws_defs ws_uses].
    + intros k dd H. destruct (N.eq_dec idx k) as [He | Hne].
      * subst k. rewrite find_add_same in H. injection H as <-.
        destruct (M.find idx (ws_defs st)) as [d0 |] eqn:Ef.
        -- destruct (Hd _ _ Ef) as [? [? ?]]. repeat split; [assumption | assumption | lia].
        -- repeat split; [exact E1 | exact E2 |].
           destruct (Nat.eqb d 0); lia.
      * rewrite find_add_other in H; [| exact Hne].
        destruct (Hd _ _ H) as [? [? ?]]. repeat split; [assumption | assumption | lia].
    + intros k u H. destruct (N.eq_dec idx k) as [He | Hne].
      * subst k. rewrite find_add_same in H. injection H as <-. lia.
      * rewrite find_add_other in H; [| exact Hne]. specialize (Hu _ _ H). lia.
  - repeat split; cbn [ws_pos ws_defs ws_uses ws_ok].
    + lia.
    + intros k dd H. destruct (N.eq_dec idx k) as [He | Hne].
      * subst k. rewrite find_add_same. rewrite H. reflexivity.
      * rewrite find_add_other; [exact H | exact Hne].
    + intros k u H. destruct (N.eq_dec idx k) as [He | Hne].
      * subst k. exists (ws_pos st). rewrite find_add_same.
        split; [reflexivity |]. specialize (Hu _ _ H). lia.
      * exists u. rewrite find_add_other; [| exact Hne]. split; [exact H | lia].
    + intros H. exact H.
Qed.

Lemma walk_wf_le : forall size,
  (forall b pc n d st, bi_size b <= size -> ws_wf pc n st ->
     ws_wf pc n (walk_instr pc n d st b) /\ ws_le st (walk_instr pc n d st b))
  /\ (forall bs pc n d st, bs_size bs <= size -> ws_wf pc n st ->
     ws_wf pc n (walk_bs pc n d st bs) /\ ws_le st (walk_bs pc n d st bs)).
Proof.
  induction size as [| s IH].
  - split.
    + intros b pc n d st Hsz. pose proof (bi_size_pos b). lia.
    + intros bs pc n d st Hsz Hwf. destruct bs as [| b r].
      * rewrite walk_bs_nil. split; [exact Hwf | apply ws_le_refl].
      * cbn [bs_size] in Hsz. pose proof (bi_size_pos b). lia.
  - destruct IH as [IHi IHl].
    assert (Hi : forall b pc n d st, bi_size b <= S s -> ws_wf pc n st ->
              ws_wf pc n (walk_instr pc n d st b)
              /\ ws_le st (walk_instr pc n d st b)).
    { intros b pc n d st Hsz Hwf. destruct b;
        try (solve [ split; [ apply ws_bump_wf; exact Hwf | apply ws_bump_le ] ]).
      - (* local.get *) rewrite walk_get_eq. apply ws_get_wf_le. exact Hwf.
      - (* local.set *) rewrite walk_set_eq. apply ws_def_wf_le. exact Hwf.
      - (* local.tee *) rewrite walk_tee_eq. apply ws_def_wf_le. exact Hwf.
      - (* block *)
        rewrite walk_block_eq.
        assert (Hsz' : bs_size l <= s) by (rewrite bi_size_block in Hsz; lia).
        destruct (IHl l pc n (S d) (ws_guard l (ws_bump st)) Hsz'
                    (ws_guard_wf pc n l _ (ws_bump_wf pc n st Hwf))) as [Hw Hle].
        split; [exact Hw |].
        eapply ws_le_trans; [| exact Hle].
        eapply ws_le_trans; [apply ws_bump_le | apply ws_guard_le].
      - (* loop *)
        rewrite walk_loop_eq.
        assert (Hsz' : bs_size l <= s) by (rewrite bi_size_loop in Hsz; lia).
        destruct (IHl l pc n (S d) (ws_guard l (ws_bump st)) Hsz'
                    (ws_guard_wf pc n l _ (ws_bump_wf pc n st Hwf))) as [Hw Hle].
        split; [exact Hw |].
        eapply ws_le_trans; [| exact Hle].
        eapply ws_le_trans; [apply ws_bump_le | apply ws_guard_le].
      - (* if *)
        rewrite walk_if_eq.
        rewrite bi_size_if in Hsz.
        assert (Hwf0 : ws_wf pc n (ws_guard l0 (ws_guard l (ws_bump st))))
          by (apply ws_guard_wf; apply ws_guard_wf; apply ws_bump_wf; exact Hwf).
        destruct (IHl l pc n (S d) _ ltac:(lia) Hwf0) as [Hw1 Hle1].
        destruct (IHl l0 pc n (S d) _ ltac:(lia) Hw1) as [Hw2 Hle2].
        split; [exact Hw2 |].
        eapply ws_le_trans; [| eapply ws_le_trans; [exact Hle1 | exact Hle2]].
        eapply ws_le_trans; [apply ws_bump_le |].
        eapply ws_le_trans; [apply ws_guard_le | apply ws_guard_le]. }
    split; [exact Hi |].
    intros bs. induction bs as [| b r IHr]; intros pc n d st Hsz Hwf.
    + rewrite walk_bs_nil. split; [exact Hwf | apply ws_le_refl].
    + rewrite walk_bs_cons. cbn [bs_size] in Hsz.
      destruct (Hi b pc n d st ltac:(lia) Hwf) as [Hw1 Hle1].
      destruct (IHr pc n d _ ltac:(lia) Hw1) as [Hw2 Hle2].
      split; [exact Hw2 | eapply ws_le_trans; [exact Hle1 | exact Hle2]].
Qed.

Lemma walk_instr_wf : forall pc n d st b,
  ws_wf pc n st -> ws_wf pc n (walk_instr pc n d st b).
Proof.
  intros pc n d st b H.
  exact (proj1 (proj1 (walk_wf_le (bi_size b)) b pc n d st (le_n _) H)).
Qed.

Lemma walk_instr_le : forall pc n d st b,
  ws_wf pc n st -> ws_le st (walk_instr pc n d st b).
Proof.
  intros pc n d st b H.
  exact (proj2 (proj1 (walk_wf_le (bi_size b)) b pc n d st (le_n _) H)).
Qed.

Lemma walk_bs_wf : forall pc n d st bs,
  ws_wf pc n st -> ws_wf pc n (walk_bs pc n d st bs).
Proof.
  intros pc n d st bs H.
  exact (proj1 (proj2 (walk_wf_le (bs_size bs)) bs pc n d st (le_n _) H)).
Qed.

Lemma walk_bs_le : forall pc n d st bs,
  ws_wf pc n st -> ws_le st (walk_bs pc n d st bs).
Proof.
  intros pc n d st bs H.
  exact (proj2 (proj2 (walk_wf_le (bs_size bs)) bs pc n d st (le_n _) H)).
Qed.

(* Liveness, half one: a local live over a stretch of code is read
   somewhere in it, and the walk records that read at a position at or
   after where the stretch begins.  So the interval's right end is at
   least the current position. *)
Lemma walk_live_use : forall size,
  (forall b pc n d st j, bi_size b <= size ->
     (pc <= j)%N -> (j < n)%N -> ws_wf pc n st ->
     bi_live j b = true ->
     ws_ok (walk_instr pc n d st b) = true ->
     exists u, M.find j (ws_uses (walk_instr pc n d st b)) = Some u
            /\ ws_pos st <= u)
  /\ (forall bs pc n d st j, bs_size bs <= size ->
     (pc <= j)%N -> (j < n)%N -> ws_wf pc n st ->
     bs_live_b j bs = true ->
     ws_ok (walk_bs pc n d st bs) = true ->
     exists u, M.find j (ws_uses (walk_bs pc n d st bs)) = Some u
            /\ ws_pos st <= u).
Proof.
  induction size as [| s IH].
  - split.
    + intros b pc n d st j Hsz. pose proof (bi_size_pos b). lia.
    + intros bs pc n d st j Hsz Hpc Hn Hwf Hlive. destruct bs as [| b r].
      * discriminate Hlive.
      * cbn [bs_size] in Hsz. pose proof (bi_size_pos b). lia.
  - destruct IH as [IHi IHl].
    assert (Hi : forall b pc n d st j, bi_size b <= S s ->
             (pc <= j)%N -> (j < n)%N -> ws_wf pc n st ->
             bi_live j b = true ->
             ws_ok (walk_instr pc n d st b) = true ->
             exists u, M.find j (ws_uses (walk_instr pc n d st b)) = Some u
                    /\ ws_pos st <= u).
    { intros b pc n d st j Hsz Hpc Hn Hwf Hlive Hok.
      destruct b; try discriminate Hlive.
      - (* local.get *)
        cbn [bi_live] in Hlive. apply N.eqb_eq in Hlive. subst l.
        rewrite walk_get_eq in Hok |- *. unfold ws_get in Hok |- *.
        assert (E1 : N.ltb j pc = false) by (apply N.ltb_ge; exact Hpc).
        assert (E2 : N.ltb j n = true) by (apply N.ltb_lt; exact Hn).
        rewrite E1, E2 in Hok |- *.
        destruct (M.mem j (ws_defs st)); [| discriminate Hok].
        exists (ws_pos st). cbn [ws_uses].
        split; [apply find_add_same | lia].
      - (* block *)
        rewrite bi_live_block in Hlive.
        rewrite walk_block_eq in Hok |- *.
        assert (Hsz' : bs_size l <= s) by (rewrite bi_size_block in Hsz; lia).
        assert (Hwf0 : ws_wf pc n (ws_guard l (ws_bump st)))
          by (apply ws_guard_wf; apply ws_bump_wf; exact Hwf).
        destruct (IHl l pc n (S d) _ j Hsz' Hpc Hn Hwf0 Hlive Hok) as [u [Hu Hge]].
        exists u. split; [exact Hu |].
        unfold ws_guard, ws_bump in Hge.
        destruct (body_ok_b l); cbn [ws_pos] in Hge; lia.
      - (* loop *)
        rewrite bi_live_loop in Hlive.
        rewrite walk_loop_eq in Hok |- *.
        assert (Hsz' : bs_size l <= s) by (rewrite bi_size_loop in Hsz; lia).
        assert (Hwf0 : ws_wf pc n (ws_guard l (ws_bump st)))
          by (apply ws_guard_wf; apply ws_bump_wf; exact Hwf).
        destruct (IHl l pc n (S d) _ j Hsz' Hpc Hn Hwf0 Hlive Hok) as [u [Hu Hge]].
        exists u. split; [exact Hu |].
        unfold ws_guard, ws_bump in Hge.
        destruct (body_ok_b l); cbn [ws_pos] in Hge; lia.
      - (* if *)
        rewrite bi_live_if in Hlive.
        rewrite walk_if_eq in Hok |- *.
        rewrite bi_size_if in Hsz.
        set (st0 := ws_guard l0 (ws_guard l (ws_bump st))) in *.
        assert (Hwf0 : ws_wf pc n st0)
          by (unfold st0; apply ws_guard_wf; apply ws_guard_wf;
              apply ws_bump_wf; exact Hwf).
        assert (Hpos0 : ws_pos st <= ws_pos st0).
        { unfold st0, ws_guard, ws_bump.
          destruct (body_ok_b l); destruct (body_ok_b l0);
            cbn [ws_pos]; lia. }
        assert (Hwf1 : ws_wf pc n (walk_bs pc n (S d) st0 l))
          by (apply walk_bs_wf; exact Hwf0).
        apply orb_true_iff in Hlive. destruct Hlive as [H1 | H2].
        + assert (Hok1 : ws_ok (walk_bs pc n (S d) st0 l) = true).
          { destruct (walk_bs_le pc n (S d) (walk_bs pc n (S d) st0 l) l0 Hwf1)
              as [_ [_ [_ Ho]]]. apply Ho. exact Hok. }
          destruct (IHl l pc n (S d) st0 j ltac:(lia) Hpc Hn Hwf0 H1 Hok1)
            as [u [Hu Hge]].
          destruct (walk_bs_le pc n (S d) (walk_bs pc n (S d) st0 l) l0 Hwf1)
            as [_ [_ [Hus _]]].
          destruct (Hus _ _ Hu) as [u' [Hu' Hle']].
          exists u'. split; [exact Hu' | lia].
        + destruct (IHl l0 pc n (S d) (walk_bs pc n (S d) st0 l) j
                      ltac:(lia) Hpc Hn Hwf1 H2 Hok) as [u [Hu Hge]].
          exists u. split; [exact Hu |].
          destruct (walk_bs_le pc n (S d) st0 l Hwf0) as [Hp _]. lia. }
    split; [exact Hi |].
    intros bs. induction bs as [| b r IHr];
      intros pc n d st j Hsz Hpc Hn Hwf Hlive Hok.
    + discriminate Hlive.
    + rewrite walk_bs_cons in Hok |- *. cbn [bs_size] in Hsz.
      cbn [bs_live_b] in Hlive.
      assert (Hwf1 : ws_wf pc n (walk_instr pc n d st b))
        by (apply walk_instr_wf; exact Hwf).
      assert (Hpos1 : ws_pos st <= ws_pos (walk_instr pc n d st b))
        by (destruct (walk_instr_le pc n d st b Hwf) as [Hp _]; exact Hp).
      apply orb_true_iff in Hlive. destruct Hlive as [H1 | H2].
      * assert (Hok1 : ws_ok (walk_instr pc n d st b) = true).
        { destruct (walk_bs_le pc n d (walk_instr pc n d st b) r Hwf1)
            as [_ [_ [_ Ho]]]. apply Ho. exact Hok. }
        destruct (Hi b pc n d st j ltac:(lia) Hpc Hn Hwf H1 Hok1) as [u [Hu Hge]].
        destruct (walk_bs_le pc n d (walk_instr pc n d st b) r Hwf1)
          as [_ [_ [Hus _]]].
        destruct (Hus _ _ Hu) as [u' [Hu' Hle']].
        exists u'. split; [exact Hu' | lia].
      * apply andb_true_iff in H2. destruct H2 as [_ H2].
        destruct (IHr pc n d (walk_instr pc n d st b) j ltac:(lia) Hpc Hn Hwf1 H2 Hok)
          as [u [Hu Hge]].
        exists u. split; [exact Hu | lia].
Qed.

(* Liveness, half two: the interval's left end.  A local live at a point
   was defined before it -- or its def is guarded, and then the walk
   opened its interval at 0, which is before everything.  Both are
   [inv_j j P]: whatever def of j the state holds is at or before P. *)
Definition inv_j (j : N) (P : nat) (st : walk_state) : Prop :=
  forall d, M.find j (ws_defs st) = Some d -> d <= P.

Lemma inv_j_bump : forall j P st, inv_j j P st -> inv_j j P (ws_bump st).
Proof. intros j P st H d Hd. apply H. exact Hd. Qed.

Lemma inv_j_guard : forall j P b st, inv_j j P st -> inv_j j P (ws_guard b st).
Proof.
  intros j P b st H d Hd. apply H. unfold ws_guard in Hd.
  destruct (body_ok_b b); [exact Hd | exact Hd].
Qed.

(* Under structured control every def the walk records is 0, so nothing
   it does can push a def past P. *)
Lemma walk_inv_nonzero : forall size,
  (forall b pc n d st j P, bi_size b <= size -> d <> 0 ->
     inv_j j P st -> inv_j j P (walk_instr pc n d st b))
  /\ (forall bs pc n d st j P, bs_size bs <= size -> d <> 0 ->
     inv_j j P st -> inv_j j P (walk_bs pc n d st bs)).
Proof.
  induction size as [| s IH].
  - split.
    + intros b pc n d st j P Hsz. pose proof (bi_size_pos b). lia.
    + intros bs pc n d st j P Hsz Hd Hinv. destruct bs as [| b r].
      * rewrite walk_bs_nil. exact Hinv.
      * cbn [bs_size] in Hsz. pose proof (bi_size_pos b). lia.
  - destruct IH as [IHi IHl].
    assert (Hi : forall b pc n d st j P, bi_size b <= S s -> d <> 0 ->
              inv_j j P st -> inv_j j P (walk_instr pc n d st b)).
    { intros b pc n d st j P Hsz Hd Hinv. destruct b;
        try (solve [ apply inv_j_bump; exact Hinv ]).
      - rewrite walk_get_eq. unfold ws_get.
        destruct (N.ltb l pc); [apply inv_j_bump; exact Hinv |].
        destruct (N.ltb l n); [| apply inv_j_bump; exact Hinv].
        destruct (M.mem l (ws_defs st));
          intros dd Hdd; apply Hinv; exact Hdd.
      - rewrite walk_set_eq. unfold ws_def.
        destruct (N.ltb l pc); [apply inv_j_bump; exact Hinv |].
        destruct (N.ltb l n); [| apply inv_j_bump; exact Hinv].
        intros dd Hdd. cbn [ws_defs] in Hdd.
        destruct (N.eq_dec l j) as [He | Hne].
        + subst l. rewrite find_add_same in Hdd. injection Hdd as <-.
          destruct (M.find j (ws_defs st)) as [d0 |] eqn:Ef;
            [ apply Hinv; exact Ef |].
          destruct d as [| d']; [ contradiction | cbn; lia ].
        + rewrite find_add_other in Hdd; [| exact Hne]. apply Hinv. exact Hdd.
      - rewrite walk_tee_eq. unfold ws_def.
        destruct (N.ltb l pc); [apply inv_j_bump; exact Hinv |].
        destruct (N.ltb l n); [| apply inv_j_bump; exact Hinv].
        intros dd Hdd. cbn [ws_defs] in Hdd.
        destruct (N.eq_dec l j) as [He | Hne].
        + subst l. rewrite find_add_same in Hdd. injection Hdd as <-.
          destruct (M.find j (ws_defs st)) as [d0 |] eqn:Ef;
            [ apply Hinv; exact Ef |].
          destruct d as [| d']; [ contradiction | cbn; lia ].
        + rewrite find_add_other in Hdd; [| exact Hne]. apply Hinv. exact Hdd.
      - rewrite walk_block_eq. apply IHl;
          [ rewrite bi_size_block in Hsz; lia | discriminate
          | apply inv_j_guard; apply inv_j_bump; exact Hinv ].
      - rewrite walk_loop_eq. apply IHl;
          [ rewrite bi_size_loop in Hsz; lia | discriminate
          | apply inv_j_guard; apply inv_j_bump; exact Hinv ].
      - rewrite walk_if_eq. rewrite bi_size_if in Hsz.
        apply IHl; [ lia | discriminate |].
        apply IHl; [ lia | discriminate |].
        apply inv_j_guard. apply inv_j_guard. apply inv_j_bump. exact Hinv. }
    split; [exact Hi |].
    intros bs. induction bs as [| b r IHr]; intros pc n d st j P Hsz Hd Hinv.
    + rewrite walk_bs_nil. exact Hinv.
    + rewrite walk_bs_cons. cbn [bs_size] in Hsz.
      apply IHr; [ lia | exact Hd |].
      apply Hi; [ lia | exact Hd | exact Hinv ].
Qed.

(* An instruction that does not kill j leaves j's def where it was: it
   either does not touch j, or writes it under structured control, where
   the interval opens at 0. *)
Lemma walk_instr_inv_nokill : forall pc n d st b j P,
  bi_kills j b = false -> inv_j j P st -> inv_j j P (walk_instr pc n d st b).
Proof.
  intros pc n d st b j P Hk Hinv. destruct b;
    try (solve [ apply inv_j_bump; exact Hinv ]).
  - rewrite walk_get_eq. unfold ws_get.
    destruct (N.ltb l pc); [apply inv_j_bump; exact Hinv |].
    destruct (N.ltb l n); [| apply inv_j_bump; exact Hinv].
    destruct (M.mem l (ws_defs st)); intros dd Hdd; apply Hinv; exact Hdd.
  - (* set: not a kill of j, so l <> j *)
    cbn [bi_kills] in Hk. apply N.eqb_neq in Hk.
    rewrite walk_set_eq. unfold ws_def.
    destruct (N.ltb l pc); [apply inv_j_bump; exact Hinv |].
    destruct (N.ltb l n); [| apply inv_j_bump; exact Hinv].
    intros dd Hdd. cbn [ws_defs] in Hdd.
    rewrite find_add_other in Hdd; [| intros He; apply Hk; symmetry; exact He].
    apply Hinv. exact Hdd.
  - cbn [bi_kills] in Hk. apply N.eqb_neq in Hk.
    rewrite walk_tee_eq. unfold ws_def.
    destruct (N.ltb l pc); [apply inv_j_bump; exact Hinv |].
    destruct (N.ltb l n); [| apply inv_j_bump; exact Hinv].
    intros dd Hdd. cbn [ws_defs] in Hdd.
    rewrite find_add_other in Hdd; [| intros He; apply Hk; symmetry; exact He].
    apply Hinv. exact Hdd.
  - rewrite walk_block_eq. apply (proj2 (walk_inv_nonzero (bs_size l)));
      [ lia | discriminate | apply inv_j_guard; apply inv_j_bump; exact Hinv ].
  - rewrite walk_loop_eq. apply (proj2 (walk_inv_nonzero (bs_size l)));
      [ lia | discriminate | apply inv_j_guard; apply inv_j_bump; exact Hinv ].
  - rewrite walk_if_eq.
    apply (proj2 (walk_inv_nonzero (bs_size l0)));
      [ lia | discriminate |].
    apply (proj2 (walk_inv_nonzero (bs_size l)));
      [ lia | discriminate |].
    apply inv_j_guard. apply inv_j_guard. apply inv_j_bump. exact Hinv.
Qed.

Lemma walk_live_start : forall size,
  (forall b pc n d st j P, bi_size b <= size ->
     (pc <= j)%N -> (j < n)%N -> ws_wf pc n st -> inv_j j P st ->
     bi_live j b = true ->
     ws_ok (walk_instr pc n d st b) = true ->
     exists dj, M.find j (ws_defs (walk_instr pc n d st b)) = Some dj /\ dj <= P)
  /\ (forall bs pc n d st j P, bs_size bs <= size ->
     (pc <= j)%N -> (j < n)%N -> ws_wf pc n st -> inv_j j P st ->
     bs_live_b j bs = true ->
     ws_ok (walk_bs pc n d st bs) = true ->
     exists dj, M.find j (ws_defs (walk_bs pc n d st bs)) = Some dj /\ dj <= P).
Proof.
  induction size as [| s IH].
  - split.
    + intros b pc n d st j P Hsz. pose proof (bi_size_pos b). lia.
    + intros bs pc n d st j P Hsz Hpc Hn Hwf Hinv Hlive. destruct bs as [| b r].
      * discriminate Hlive.
      * cbn [bs_size] in Hsz. pose proof (bi_size_pos b). lia.
  - destruct IH as [IHi IHl].
    assert (Hi : forall b pc n d st j P, bi_size b <= S s ->
             (pc <= j)%N -> (j < n)%N -> ws_wf pc n st -> inv_j j P st ->
             bi_live j b = true ->
             ws_ok (walk_instr pc n d st b) = true ->
             exists dj, M.find j (ws_defs (walk_instr pc n d st b)) = Some dj
                     /\ dj <= P).
    { intros b pc n d st j P Hsz Hpc Hn Hwf Hinv Hlive Hok.
      destruct b; try discriminate Hlive.
      - (* local.get: the walk only got here because j was already defined *)
        cbn [bi_live] in Hlive. apply N.eqb_eq in Hlive. subst l.
        rewrite walk_get_eq in Hok |- *. unfold ws_get in Hok |- *.
        assert (E1 : N.ltb j pc = false) by (apply N.ltb_ge; exact Hpc).
        assert (E2 : N.ltb j n = true) by (apply N.ltb_lt; exact Hn).
        rewrite E1, E2 in Hok |- *.
        destruct (M.mem j (ws_defs st)) eqn:Emem; [| discriminate Hok].
        cbn [ws_defs].
        apply MF.mem_in_iff in Emem. apply MF.in_find_iff in Emem.
        destruct (M.find j (ws_defs st)) as [dj |] eqn:Ef;
          [| exfalso; apply Emem; reflexivity ].
        exists dj. split; [reflexivity | apply Hinv; exact Ef].
      - (* block *)
        rewrite bi_live_block in Hlive.
        rewrite walk_block_eq in Hok |- *.
        apply (IHl l pc n (S d) _ j P);
          [ rewrite bi_size_block in Hsz; lia | exact Hpc | exact Hn
          | apply ws_guard_wf; apply ws_bump_wf; exact Hwf
          | apply inv_j_guard; apply inv_j_bump; exact Hinv
          | exact Hlive | exact Hok ].
      - (* loop *)
        rewrite bi_live_loop in Hlive.
        rewrite walk_loop_eq in Hok |- *.
        apply (IHl l pc n (S d) _ j P);
          [ rewrite bi_size_loop in Hsz; lia | exact Hpc | exact Hn
          | apply ws_guard_wf; apply ws_bump_wf; exact Hwf
          | apply inv_j_guard; apply inv_j_bump; exact Hinv
          | exact Hlive | exact Hok ].
      - (* if: the def may sit in the branch not taken, and that is
           exactly the case the interval opening at 0 covers *)
        rewrite bi_live_if in Hlive.
        rewrite walk_if_eq in Hok |- *.
        rewrite bi_size_if in Hsz.
        set (st0 := ws_guard l0 (ws_guard l (ws_bump st))) in *.
        assert (Hwf0 : ws_wf pc n st0)
          by (unfold st0; apply ws_guard_wf; apply ws_guard_wf;
              apply ws_bump_wf; exact Hwf).
        assert (Hinv0 : inv_j j P st0)
          by (unfold st0; apply inv_j_guard; apply inv_j_guard;
              apply inv_j_bump; exact Hinv).
        assert (Hwf1 : ws_wf pc n (walk_bs pc n (S d) st0 l))
          by (apply walk_bs_wf; exact Hwf0).
        apply orb_true_iff in Hlive. destruct Hlive as [H1 | H2].
        + assert (Hok1 : ws_ok (walk_bs pc n (S d) st0 l) = true).
          { destruct (walk_bs_le pc n (S d) (walk_bs pc n (S d) st0 l) l0 Hwf1)
              as [_ [_ [_ Ho]]]. apply Ho. exact Hok. }
          destruct (IHl l pc n (S d) st0 j P ltac:(lia) Hpc Hn Hwf0 Hinv0 H1 Hok1)
            as [dj [Hdj Hle]].
          destruct (walk_bs_le pc n (S d) (walk_bs pc n (S d) st0 l) l0 Hwf1)
            as [_ [Hdefs _]].
          exists dj. split; [apply Hdefs; exact Hdj | exact Hle].
        + apply (IHl l0 pc n (S d) _ j P);
            [ lia | exact Hpc | exact Hn | exact Hwf1
            | apply (proj2 (walk_inv_nonzero (bs_size l)));
              [ lia | discriminate | exact Hinv0 ]
            | exact H2 | exact Hok ]. }
    split; [exact Hi |].
    intros bs. induction bs as [| b r IHr];
      intros pc n d st j P Hsz Hpc Hn Hwf Hinv Hlive Hok.
    + discriminate Hlive.
    + rewrite walk_bs_cons in Hok |- *. cbn [bs_size] in Hsz.
      cbn [bs_live_b] in Hlive.
      assert (Hwf1 : ws_wf pc n (walk_instr pc n d st b))
        by (apply walk_instr_wf; exact Hwf).
      apply orb_true_iff in Hlive. destruct Hlive as [H1 | H2].
      * assert (Hok1 : ws_ok (walk_instr pc n d st b) = true).
        { destruct (walk_bs_le pc n d (walk_instr pc n d st b) r Hwf1)
            as [_ [_ [_ Ho]]]. apply Ho. exact Hok. }
        destruct (Hi b pc n d st j P ltac:(lia) Hpc Hn Hwf Hinv H1 Hok1)
          as [dj [Hdj Hle]].
        destruct (walk_bs_le pc n d (walk_instr pc n d st b) r Hwf1)
          as [_ [Hdefs _]].
        exists dj. split; [apply Hdefs; exact Hdj | exact Hle].
      * apply andb_true_iff in H2. destruct H2 as [Hnk H2].
        apply negb_true_iff in Hnk.
        apply (IHr pc n d (walk_instr pc n d st b) j P);
          [ lia | exact Hpc | exact Hn | exact Hwf1
          | apply walk_instr_inv_nokill; [exact Hnk | exact Hinv]
          | exact H2 | exact Hok ].
Qed.

(* ── 4. from the walk's maps to phi ───────────────────────────────── *)

Lemma walk_pos : forall size,
  (forall b pc n d st, bi_size b <= size ->
     ws_pos (walk_instr pc n d st b) = ws_pos st + bi_size b)
  /\ (forall bs pc n d st, bs_size bs <= size ->
     ws_pos (walk_bs pc n d st bs) = ws_pos st + bs_size bs).
Proof.
  induction size as [| s IH].
  - split.
    + intros b pc n d st Hsz. pose proof (bi_size_pos b). lia.
    + intros bs pc n d st Hsz. destruct bs as [| b r].
      * rewrite walk_bs_nil. cbn [bs_size]. lia.
      * cbn [bs_size] in Hsz. pose proof (bi_size_pos b). lia.
  - destruct IH as [IHi IHl].
    assert (Hi : forall b pc n d st, bi_size b <= S s ->
              ws_pos (walk_instr pc n d st b) = ws_pos st + bi_size b).
    { intros b pc n d st Hsz. destruct b;
        try (solve [ cbn [walk_instr bi_size ws_bump ws_pos]; lia ]).
      - rewrite walk_get_eq. unfold ws_get.
        destruct (N.ltb l pc); [cbn [ws_bump ws_pos bi_size]; lia |].
        destruct (N.ltb l n); [| cbn [ws_bump ws_pos bi_size]; lia].
        destruct (M.mem l (ws_defs st)); cbn [ws_pos bi_size]; lia.
      - rewrite walk_set_eq. unfold ws_def.
        destruct (N.ltb l pc); [cbn [ws_bump ws_pos bi_size]; lia |].
        destruct (N.ltb l n); [| cbn [ws_bump ws_pos bi_size]; lia].
        cbn [ws_pos bi_size]; lia.
      - rewrite walk_tee_eq. unfold ws_def.
        destruct (N.ltb l pc); [cbn [ws_bump ws_pos bi_size]; lia |].
        destruct (N.ltb l n); [| cbn [ws_bump ws_pos bi_size]; lia].
        cbn [ws_pos bi_size]; lia.
      - rewrite walk_block_eq, bi_size_block.
        rewrite IHl; [| rewrite bi_size_block in Hsz; lia].
        unfold ws_guard, ws_bump. destruct (body_ok_b l); cbn [ws_pos]; lia.
      - rewrite walk_loop_eq, bi_size_loop.
        rewrite IHl; [| rewrite bi_size_loop in Hsz; lia].
        unfold ws_guard, ws_bump. destruct (body_ok_b l); cbn [ws_pos]; lia.
      - rewrite walk_if_eq, bi_size_if. rewrite bi_size_if in Hsz.
        rewrite IHl; [| lia]. rewrite IHl; [| lia].
        unfold ws_guard, ws_bump.
        destruct (body_ok_b l); destruct (body_ok_b l0); cbn [ws_pos]; lia. }
    split; [exact Hi |].
    intros bs. induction bs as [| b r IHr]; intros pc n d st Hsz.
    + rewrite walk_bs_nil. cbn [bs_size]. lia.
    + rewrite walk_bs_cons. cbn [bs_size] in Hsz |- *.
      rewrite IHr; [| lia]. rewrite Hi; [| lia]. lia.
Qed.

Lemma walk_bs_pos : forall pc n d st bs,
  ws_pos (walk_bs pc n d st bs) = ws_pos st + bs_size bs.
Proof. intros. apply (proj2 (walk_pos (bs_size bs))). lia. Qed.

Lemma walk_instr_pos : forall pc n d st b,
  ws_pos (walk_instr pc n d st b) = ws_pos st + bi_size b.
Proof. intros. apply (proj1 (walk_pos (bi_size b))). lia. Qed.

(* extract_intervals reads the two maps off together. *)
Lemma elements_in : forall (m : M.t nat) k v,
  M.find k m = Some v -> In (k, v) (M.elements m).
Proof.
  intros m k v H. apply M.find_2 in H. apply M.elements_1 in H.
  induction (M.elements m) as [| [k' v'] l IHl]; [inversion H |].
  apply InA_cons in H. destruct H as [Heq | Hin].
  - destruct Heq as [Hk Hv]. cbn in Hk, Hv. subst k' v'. left. reflexivity.
  - right. apply IHl. exact Hin.
Qed.

Lemma in_elements_find : forall (m : M.t nat) k v,
  In (k, v) (M.elements m) -> M.find k m = Some v.
Proof.
  intros m k v H. apply M.find_1. apply M.elements_2.
  apply InA_alt. exists (k, v). split; [| exact H].
  split; reflexivity.
Qed.

Lemma extract_in : forall st k d u,
  M.find k (ws_defs st) = Some d ->
  M.find k (ws_uses st) = Some u ->
  In (k, d, u) (extract_intervals st).
Proof.
  intros st k d u Hd Hu. unfold extract_intervals.
  apply in_map_iff. exists (k, d). rewrite Hu. split; [reflexivity |].
  apply elements_in. exact Hd.
Qed.

Lemma extract_local : forall st x,
  In x (extract_intervals st) ->
  exists d, M.find (iv_local x) (ws_defs st) = Some d.
Proof.
  intros st x H. unfold extract_intervals in H. apply in_map_iff in H.
  destruct H as [[k dk] [Heq Hin]].
  destruct (M.find k (ws_uses st)); subst x; cbn [iv_local];
    exists dk; apply in_elements_find; exact Hin.
Qed.

Lemma extract_locals_eq : forall st,
  List.map iv_local (extract_intervals st)
    = List.map fst (M.elements (ws_defs st)).
Proof.
  intros st. unfold extract_intervals. rewrite map_map.
  apply map_ext. intros [k dk].
  destruct (M.find k (ws_uses st)); reflexivity.
Qed.

Lemma nodupa_key_nodup : forall (l : list (N * nat)),
  NoDupA (@M.eq_key nat) l -> NoDup (List.map fst l).
Proof.
  intros l. induction l as [| [k v] r IH]; intros H; cbn [List.map]; [constructor |].
  inversion H as [| x xs Hnin Hnd Heq]; subst. constructor.
  - intros Hin. apply Hnin. apply in_map_iff in Hin.
    destruct Hin as [[k' v'] [Heq' Hin']]. cbn in Heq'. subst k'.
    apply InA_alt. exists (k, v'). split; [reflexivity | exact Hin'].
  - apply IH. exact Hnd.
Qed.

Lemma extract_nodup : forall st, NoDup (List.map iv_local (extract_intervals st)).
Proof.
  intros st. rewrite extract_locals_eq. apply nodupa_key_nodup.
  apply M.elements_3w.
Qed.

Lemma extract_range : forall pc n st x,
  ws_wf pc n st -> In x (extract_intervals st) ->
  (pc <= iv_local x)%N /\ (iv_local x < n)%N.
Proof.
  intros pc n st x [Hd _] Hin. destruct (extract_local st x Hin) as [dx Hdx].
  destruct (Hd _ _ Hdx) as [Hlo [Hhi _]]. split; assumption.
Qed.

(* One interval per coalescable slot, and they are distinct, so there are
   never more intervals than slots.  This is the cardinality the scan's
   free-slot search runs on. *)
Lemma extract_length : forall pc n st,
  ws_wf pc n st -> length (extract_intervals st) <= N.to_nat n - N.to_nat pc.
Proof.
  intros pc n st Hwf.
  assert (Hincl : incl (List.map iv_local (extract_intervals st))
                       (List.map N.of_nat
                          (seq (N.to_nat pc) (N.to_nat n - N.to_nat pc)))).
  { intros k Hk. apply in_map_iff in Hk. destruct Hk as [x [Heq Hin]].
    destruct (extract_range pc n st x Hwf Hin) as [Hlo Hhi].
    apply in_map_iff. exists (N.to_nat k). split.
    - apply N2Nat.id.
    - apply in_seq. subst k. lia. }
  pose proof (NoDup_incl_length (extract_nodup st) Hincl) as Hle.
  rewrite length_map in Hle. rewrite length_map, length_seq in Hle. exact Hle.
Qed.

Lemma scan_range : forall tys pc n t ivs,
  tys_uniform tys pc n t ->
  (forall x, In x ivs -> (pc <= iv_local x)%N /\ (iv_local x < n)%N) ->
  forall active phi,
  length active + length ivs <= N.to_nat n - N.to_nat pc ->
  (forall k sl, M.find k phi = Some sl -> (pc <= sl)%N /\ (sl < n)%N) ->
  forall k sl, M.find k (linear_scan_loop tys pc n ivs active phi) = Some sl ->
    (pc <= sl)%N /\ (sl < n)%N.
Proof.
  intros tys pc n t ivs Huni.
  induction ivs as [| [[h sh] eh] rest IH];
    intros Hrange active phi Hcard Hphi k sl Hk.
  - exact (Hphi _ _ Hk).
  - cbn [linear_scan_loop] in Hk.
    assert (Hlen : length (expire_active sh active) <= length active)
      by apply expire_length.
    assert (Hlt : length (expire_active sh active) < N.to_nat n - N.to_nat pc)
      by (cbn in Hcard; lia).
    assert (Hty : lookup_N tys h = Some t).
    { destruct (Hrange (h, sh, eh) (or_introl eq_refl)) as [Hlo Hhi].
      cbn in Hlo, Hhi. apply Huni; assumption. }
    destruct (find_free_slot_free tys pc n h (expire_active sh active) t
                Hty Huni Hlt) as [Hlo' [Hhi' _]].
    cbn zeta in Hlo', Hhi'.
    assert (Hcard' :
      length ((find_free_slot tys pc n h (expire_active sh active), eh)
                :: expire_active sh active) + length rest
      <= N.to_nat n - N.to_nat pc) by (cbn in Hcard |- *; lia).
    assert (Hphi' : forall k' sl',
      M.find k' (M.add h (find_free_slot tys pc n h (expire_active sh active))
                   phi) = Some sl' -> (pc <= sl')%N /\ (sl' < n)%N).
    { intros k' sl' Hk'. destruct (N.eq_dec h k') as [He | Hne].
      - subst k'. rewrite find_add_same in Hk'. injection Hk' as <-.
        split; assumption.
      - rewrite find_add_other in Hk'; [| exact Hne]. exact (Hphi _ _ Hk'). }
    exact (IH (fun x Hx => Hrange x (or_intror Hx)) _ _ Hcard' Hphi' k sl Hk).
Qed.

Lemma phi_range : forall tys pc n t st k sl,
  tys_uniform tys pc n t -> ws_wf pc n st ->
  M.find k (linear_scan tys pc n (extract_intervals st)) = Some sl ->
  (pc <= sl)%N /\ (sl < n)%N.
Proof.
  intros tys pc n t st k sl Huni Hwf H. unfold linear_scan in H.
  assert (Hperm : Permutation (sort_by_def (extract_intervals st))
                              (extract_intervals st)) by apply sort_by_def_perm.
  apply (scan_range tys pc n t _ Huni
           (fun x Hx => extract_range pc n st x Hwf (Permutation_in _ Hperm Hx))
           [] empty
           ltac:(cbn; rewrite (Permutation_length Hperm);
                 apply extract_length; exact Hwf)
           ltac:(intros k' sl' Hk'; rewrite MF.empty_o in Hk'; discriminate Hk')
           k sl H).
Qed.

Lemma phi_id_unassigned : forall tys pc n st k,
  M.find k (ws_defs st) = None ->
  apply_phi_local (linear_scan tys pc n (extract_intervals st)) k = k.
Proof.
  intros tys pc n st k H. unfold apply_phi_local, linear_scan.
  rewrite scan_preserves.
  - rewrite MF.empty_o. reflexivity.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq Hin]].
    apply (Permutation_in _ (sort_by_def_perm (extract_intervals st))) in Hin.
    destruct (extract_local st x Hin) as [dx Hdx].
    rewrite Heq in Hdx. rewrite H in Hdx. discriminate Hdx.
Qed.

(* Overlapping intervals, in the walk's own terms. *)
Lemma phi_overlap_distinct : forall tys pc n t st i j di ui dj uj,
  tys_uniform tys pc n t -> ws_wf pc n st ->
  M.find i (ws_defs st) = Some di -> M.find i (ws_uses st) = Some ui ->
  M.find j (ws_defs st) = Some dj -> M.find j (ws_uses st) = Some uj ->
  i <> j -> di <= uj -> dj <= ui ->
  apply_phi_local (linear_scan tys pc n (extract_intervals st)) i
    <> apply_phi_local (linear_scan tys pc n (extract_intervals st)) j.
Proof.
  intros tys pc n t st i j di ui dj uj Huni Hwf Hdi Hui Hdj Huj Hij Hiu Hju.
  apply (linear_scan_disjoint tys pc n t (extract_intervals st) i di ui j dj uj);
    [ exact Huni
    | intros x Hx; apply (extract_range pc n st x Hwf Hx)
    | apply extract_nodup
    | apply extract_length; exact Hwf
    | apply extract_in; assumption
    | apply extract_in; assumption
    | exact Hij | exact Hiu | exact Hju ].
Qed.

Lemma scan_assigned : forall tys pc n ivs active phi k,
  In k (List.map iv_local ivs) ->
  exists sl, M.find k (linear_scan_loop tys pc n ivs active phi) = Some sl.
Proof.
  intros tys pc n ivs.
  induction ivs as [| [[h sh] eh] rest IH]; intros active phi k Hin.
  - destruct Hin.
  - cbn [linear_scan_loop]. cbn [List.map iv_local] in Hin.
    destruct Hin as [He | Hin].
    + subst h. eapply scan_keeps_some. apply find_add_same.
    + apply IH. exact Hin.
Qed.

Lemma phi_out_of_range : forall tys pc n stf j,
  ws_wf pc n stf -> ~ ((pc <= j)%N /\ (j < n)%N) ->
  apply_phi_local (linear_scan tys pc n (extract_intervals stf)) j = j.
Proof.
  intros tys pc n stf j Hwf Hnr. apply phi_id_unassigned.
  destruct (M.find j (ws_defs stf)) as [d |] eqn:E; [| reflexivity].
  exfalso. destruct Hwf as [Hd _]. destruct (Hd _ _ E) as [H1 [H2 _]].
  apply Hnr. split; assumption.
Qed.

Lemma phi_in_range : forall tys pc n t stf j dj,
  tys_uniform tys pc n t -> ws_wf pc n stf ->
  M.find j (ws_defs stf) = Some dj ->
  (pc <= apply_phi_local (linear_scan tys pc n (extract_intervals stf)) j)%N
  /\ (apply_phi_local (linear_scan tys pc n (extract_intervals stf)) j < n)%N.
Proof.
  intros tys pc n t stf j dj Huni Hwf Hd.
  assert (Hin : In j (List.map iv_local (extract_intervals stf))).
  { rewrite extract_locals_eq. apply in_map_iff. exists (j, dj).
    split; [reflexivity | apply elements_in; exact Hd]. }
  assert (Hin' : In j (List.map iv_local (sort_by_def (extract_intervals stf)))).
  { apply in_map_iff in Hin. destruct Hin as [x [Heq Hx]].
    apply in_map_iff. exists x. split; [exact Heq |].
    apply (Permutation_in _ (Permutation_sym (sort_by_def_perm _))). exact Hx. }
  destruct (scan_assigned tys pc n _ [] empty j Hin') as [sl Hsl].
  unfold apply_phi_local, linear_scan. rewrite Hsl.
  exact (phi_range tys pc n t stf j sl Huni Hwf Hsl).
Qed.

(* ── 5. the relation, built from the walk ─────────────────────────── *)

Definition defs_le (A : nat) (st : walk_state) : Prop :=
  forall k dk, M.find k (ws_defs st) = Some dk -> dk <= A.

(* Every local the context can still read has its interval reaching the
   anchor A from the left and E from the right.  At depth 0 the anchor
   is the current position and E is the end of the list, which is where
   the context's reads are; under structured control both collapse to
   the position of the enclosing construct, because every def inside it
   opens at 0. *)
Definition K_anchored (pc n : N) (stf : walk_state) (A E : nat)
  (K : N -> Prop) : Prop :=
  forall j, K j -> (pc <= j)%N -> (j < n)%N ->
    exists dj uj, M.find j (ws_defs stf) = Some dj
               /\ M.find j (ws_uses stf) = Some uj
               /\ dj <= A /\ E <= uj.

Lemma guard_ok : forall b st,
  ws_ok (ws_guard b st) = true -> body_ok_b b = true /\ ws_ok st = true.
Proof.
  intros b st H. unfold ws_guard in H. destruct (body_ok_b b) eqn:E.
  - split; [reflexivity | exact H].
  - cbn [ws_ok] in H. discriminate H.
Qed.

Lemma defs_le_bump : forall A st, defs_le A st -> defs_le A (ws_bump st).
Proof. intros A st H k dk Hk. apply (H k). exact Hk. Qed.

Lemma defs_le_guard : forall A b st, defs_le A st -> defs_le A (ws_guard b st).
Proof.
  intros A b st H k dk Hk. apply (H k). unfold ws_guard in Hk.
  destruct (body_ok_b b); exact Hk.
Qed.

Lemma defs_le_nonzero : forall pc n d st bs A,
  d <> 0 -> defs_le A st -> defs_le A (walk_bs pc n d st bs).
Proof.
  intros pc n d st bs A Hd H k dk Hk.
  exact (proj2 (walk_inv_nonzero (bs_size bs)) bs pc n d st k A
           (le_n _) Hd (fun dd Hdd => H k dd Hdd) dk Hk).
Qed.

(* One instruction cannot push a def past the anchor: at depth 0 the
   anchor is the position it records, and deeper it records 0. *)
Lemma walk_instr_defs_le : forall pc n d st b A,
  ws_wf pc n st -> defs_le A st -> (d = 0 -> A = ws_pos st) ->
  defs_le A (walk_instr pc n d st b).
Proof.
  intros pc n d st b A Hwf HA HA0. destruct b;
    try (solve [ apply defs_le_bump; exact HA ]).
  - rewrite walk_get_eq. unfold ws_get.
    destruct (N.ltb l pc); [apply defs_le_bump; exact HA |].
    destruct (N.ltb l n); [| apply defs_le_bump; exact HA].
    destruct (M.mem l (ws_defs st)); intros k dk Hk; apply (HA k); exact Hk.
  - rewrite walk_set_eq. unfold ws_def.
    destruct (N.ltb l pc); [apply defs_le_bump; exact HA |].
    destruct (N.ltb l n); [| apply defs_le_bump; exact HA].
    intros k dk Hk. cbn [ws_defs] in Hk.
    destruct (N.eq_dec l k) as [He | Hne].
    + subst l. rewrite find_add_same in Hk. injection Hk as <-.
      destruct (M.find k (ws_defs st)) as [d0 |] eqn:Ef; [apply (HA k); exact Ef |].
      destruct d as [| d']; [ rewrite (HA0 eq_refl); cbn; lia | cbn; lia ].
    + rewrite find_add_other in Hk; [| exact Hne]. apply (HA k). exact Hk.
  - rewrite walk_tee_eq. unfold ws_def.
    destruct (N.ltb l pc); [apply defs_le_bump; exact HA |].
    destruct (N.ltb l n); [| apply defs_le_bump; exact HA].
    intros k dk Hk. cbn [ws_defs] in Hk.
    destruct (N.eq_dec l k) as [He | Hne].
    + subst l. rewrite find_add_same in Hk. injection Hk as <-.
      destruct (M.find k (ws_defs st)) as [d0 |] eqn:Ef; [apply (HA k); exact Ef |].
      destruct d as [| d']; [ rewrite (HA0 eq_refl); cbn; lia | cbn; lia ].
    + rewrite find_add_other in Hk; [| exact Hne]. apply (HA k). exact Hk.
  - rewrite walk_block_eq. apply defs_le_nonzero; [discriminate |].
    apply defs_le_guard. apply defs_le_bump. exact HA.
  - rewrite walk_loop_eq. apply defs_le_nonzero; [discriminate |].
    apply defs_le_guard. apply defs_le_bump. exact HA.
  - rewrite walk_if_eq.
    apply defs_le_nonzero; [discriminate |].
    apply defs_le_nonzero; [discriminate |].
    apply defs_le_guard. apply defs_le_guard. apply defs_le_bump. exact HA.
Qed.


(* Given the intervals of the local being written and of a local the
   continuation can still read, [slot_free] is exactly disjointness of
   slots.  Out-of-range indices -- parameters, and anything past the
   declared locals -- are handled by phi being the identity on them and
   never assigning a slot outside [pc, n). *)
Lemma slot_free_from_intervals :
  forall tys pc n t stf phi L i,
  phi = linear_scan tys pc n (extract_intervals stf) ->
  tys_uniform tys pc n t ->
  ws_wf pc n stf ->
  ((pc <= i)%N -> (i < n)%N ->
     exists di ui, M.find i (ws_defs stf) = Some di
                /\ M.find i (ws_uses stf) = Some ui) ->
  (forall j, L j -> (pc <= j)%N -> (j < n)%N ->
     exists dj uj, M.find j (ws_defs stf) = Some dj
                /\ M.find j (ws_uses stf) = Some uj) ->
  (forall j dj uj di ui, L j -> j <> i -> (pc <= j)%N -> (j < n)%N ->
     (pc <= i)%N -> (i < n)%N ->
     M.find j (ws_defs stf) = Some dj -> M.find j (ws_uses stf) = Some uj ->
     M.find i (ws_defs stf) = Some di -> M.find i (ws_uses stf) = Some ui ->
     dj <= ui /\ di <= uj) ->
  slot_free phi L i.
Proof.
  intros tys pc n t stf phi L i Hphi Huni Hwf Hi Hjex Hov j Hjl Hji. subst phi.
  assert (Hdec : forall x, ((pc <= x)%N /\ (x < n)%N)
                        \/ ~ ((pc <= x)%N /\ (x < n)%N)).
  { intros x. destruct (N.le_gt_cases pc x) as [H1 | H1].
    - destruct (N.lt_ge_cases x n) as [H2 | H2].
      + left. split; assumption.
      + right. intros [_ Hc]. lia.
    - right. intros [Hc _]. lia. }
  destruct (Hdec i) as [[Hilo Hihi] | Hiout];
  destruct (Hdec j) as [[Hjlo Hjhi] | Hjout].
  - destruct (Hi Hilo Hihi) as [di [ui [Hdi Hui]]].
    destruct (Hjex j Hjl Hjlo Hjhi) as [dj [uj [Hdj Huj]]].
    destruct (Hov j dj uj di ui Hjl Hji Hjlo Hjhi Hilo Hihi Hdj Huj Hdi Hui)
      as [H1 H2].
    exact (phi_overlap_distinct tys pc n t stf j i dj uj di ui
             Huni Hwf Hdj Huj Hdi Hui Hji H1 H2).
  - destruct (Hi Hilo Hihi) as [di [ui [Hdi Hui]]].
    rewrite (phi_out_of_range tys pc n stf j Hwf Hjout).
    destruct (phi_in_range tys pc n t stf i di Huni Hwf Hdi) as [Hlo' Hhi'].
    intros Hc. apply Hjout. rewrite Hc. split; assumption.
  - destruct (Hjex j Hjl Hjlo Hjhi) as [dj [uj [Hdj Huj]]].
    rewrite (phi_out_of_range tys pc n stf i Hwf Hiout).
    destruct (phi_in_range tys pc n t stf j dj Huni Hwf Hdj) as [Hlo' Hhi'].
    intros Hc. apply Hiout. rewrite <- Hc. split; assumption.
  - rewrite (phi_out_of_range tys pc n stf j Hwf Hjout).
    rewrite (phi_out_of_range tys pc n stf i Hwf Hiout).
    exact Hji.
Qed.

(* The write's own interval: the def it records is at or before the
   current position -- it is that position at depth 0, and 0 under
   structured control -- and the use it records is that position. *)
Lemma ws_def_interval : forall pc n d st i,
  ws_wf pc n st -> (pc <= i)%N -> (i < n)%N ->
  exists di, M.find i (ws_defs (ws_def pc n d st i)) = Some di
          /\ di <= ws_pos st
          /\ M.find i (ws_uses (ws_def pc n d st i)) = Some (ws_pos st).
Proof.
  intros pc n d st i Hwf Hlo Hhi. unfold ws_def.
  assert (E1 : N.ltb i pc = false) by (apply N.ltb_ge; exact Hlo).
  assert (E2 : N.ltb i n = true) by (apply N.ltb_lt; exact Hhi).
  rewrite E1, E2. cbn [ws_defs ws_uses].
  eexists. split; [apply find_add_same | split; [| apply find_add_same]].
  destruct (M.find i (ws_defs st)) as [d0 |] eqn:Ef.
  - destruct Hwf as [Hd _]. destruct (Hd _ _ Ef) as [_ [_ H]]. exact H.
  - destruct (Nat.eqb d 0); lia.
Qed.

(* The relation, read off the walk.  Every hypothesis is either an
   invariant proved above or the anchor discipline: at depth 0 the anchor
   A is the current position and E is past the end of the list, which is
   where the context's reads are; under structured control both stay put
   at the enclosing construct, because every def inside opens at 0 and so
   cannot outrun them.  That is what makes the loop case go through: a
   write inside a loop body is guarded, so its interval starts at 0 and
   overlaps every local the body reads, however early. *)
Lemma rel_bs_of_walk : forall size tys pc n t stf phi bs d st A E K,
  phi = linear_scan tys pc n (extract_intervals stf) ->
  bs_size bs <= size ->
  tys_uniform tys pc n t ->
  ws_wf pc n stf ->
  ws_wf pc n st ->
  ws_ok (walk_bs pc n d st bs) = true ->
  ws_le (walk_bs pc n d st bs) stf ->
  defs_le A st ->
  A <= ws_pos st ->
  (d = 0 -> A = ws_pos st) ->
  defs_le E (walk_bs pc n d st bs) ->
  A <= E ->
  (d = 0 -> ws_pos st + bs_size bs <= E) ->
  K_anchored pc n stf A E K ->
  rel_bs phi K bs (List.map (apply_phi phi) bs).
Proof.
  induction size as [| s IH];
    intros tys pc n t stf phi bs d st A E K Hphi Hsz Huni Hwff Hwf Hok Hle
           HA HAle HA0 HE HAE HE2 HK.
  - destruct bs as [| b r]; [ cbn [List.map]; apply relbs_nil |].
    cbn [bs_size] in Hsz. pose proof (bi_size_pos b). lia.
  - destruct bs as [| b r]; [ cbn [List.map]; apply relbs_nil |].
    cbn [bs_size] in Hsz.
    rewrite walk_bs_cons in Hok, Hle, HE.
    assert (Hwfb : ws_wf pc n (walk_instr pc n d st b))
      by (apply walk_instr_wf; exact Hwf).
    assert (Hleb : ws_le (walk_instr pc n d st b)
                         (walk_bs pc n d (walk_instr pc n d st b) r))
      by (apply walk_bs_le; exact Hwfb).
    assert (Hokb : ws_ok (walk_instr pc n d st b) = true)
      by (destruct Hleb as [_ [_ [_ Ho]]]; apply Ho; exact Hok).
    assert (Hposb : ws_pos (walk_instr pc n d st b) = ws_pos st + bi_size b)
      by apply walk_instr_pos.
    pose proof (bi_size_pos b) as Hbpos.
    assert (HAb : defs_le A (walk_instr pc n d st b))
      by (apply walk_instr_defs_le; assumption).
    assert (Hlestf : ws_le (walk_instr pc n d st b) stf)
      by (eapply ws_le_trans; [exact Hleb | exact Hle]).
    (* every local the continuation can still read has an interval that
       reaches back to the anchor and forward past the current write *)
    assert (Hjint : forall j, bs_live_ext r K j -> (pc <= j)%N -> (j < n)%N ->
              exists dj uj, M.find j (ws_defs stf) = Some dj
                         /\ M.find j (ws_uses stf) = Some uj
                         /\ dj <= A /\ (ws_pos st <= uj \/ E <= uj)).
    { intros j Hj Hjlo Hjhi. unfold bs_live_ext in Hj.
      destruct Hj as [Hlive | [_ HKj]].
      - destruct ((proj2 (walk_live_start (bs_size r))) r pc n d
                    (walk_instr pc n d st b) j A (le_n _) Hjlo Hjhi Hwfb
                    (fun dd Hdd => HAb j dd Hdd) Hlive Hok) as [dj [Hdj Hdjle]].
        destruct ((proj2 (walk_live_use (bs_size r))) r pc n d
                    (walk_instr pc n d st b) j (le_n _) Hjlo Hjhi Hwfb Hlive Hok)
          as [uj [Huj Hujge]].
        destruct Hle as [_ [Hdefs [Huses _]]].
        destruct (Huses _ _ Huj) as [uj' [Huj' Hle']].
        exists dj, uj'. split; [apply Hdefs; exact Hdj |].
        split; [exact Huj' | split; [exact Hdjle | left; lia]].
      - destruct (HK j HKj Hjlo Hjhi) as [dj [uj [Hdj [Huj [Hd1 Hd2]]]]].
        exists dj, uj. split; [exact Hdj | split; [exact Huj |]].
        split; [exact Hd1 | right; exact Hd2]. }
    assert (HKb : K_anchored pc n stf A A (bs_live_ext r K)).
    { intros j Hj Hjlo Hjhi. destruct (Hjint j Hj Hjlo Hjhi)
        as [dj [uj [Hdj [Huj [Hd1 Hd2]]]]].
      exists dj, uj. split; [exact Hdj | split; [exact Huj |]].
      split; [exact Hd1 | destruct Hd2; lia]. }
    assert (Htail : rel_bs phi K r (List.map (apply_phi phi) r)).
    { apply (IH tys pc n t stf phi r d (walk_instr pc n d st b)
               (if Nat.eqb d 0 then ws_pos (walk_instr pc n d st b) else A) E K).
      - exact Hphi.
      - lia.
      - exact Huni.
      - exact Hwff.
      - exact Hwfb.
      - exact Hok.
      - exact Hle.
      - destruct (Nat.eqb d 0); [| exact HAb].
        intros k dk Hk. destruct Hwfb as [Hdd _].
        destruct (Hdd _ _ Hk) as [_ [_ Hx]]. exact Hx.
      - destruct (Nat.eqb d 0); lia.
      - intros Hd0. rewrite Hd0. cbn [Nat.eqb]. reflexivity.
      - exact HE.
      - destruct (Nat.eqb d 0) eqn:Ed0; [| exact HAE].
        apply PeanoNat.Nat.eqb_eq in Ed0. specialize (HE2 Ed0).
        cbn [bs_size] in HE2. lia.
      - intros Hd0. specialize (HE2 Hd0). cbn [bs_size] in HE2. lia.
      - intros j Hj Hjlo Hjhi. destruct (HK j Hj Hjlo Hjhi)
          as [dj [uj [Hdj [Huj [Hd1 Hd2]]]]].
        exists dj, uj. split; [exact Hdj | split; [exact Huj |]].
        split; [destruct (Nat.eqb d 0); lia | exact Hd2]. }
    cbn [List.map]. apply relbs_cons; [| exact Htail].
    (* the write obligation, for local.set and local.tee alike *)
    assert (Hwrite : forall i, walk_instr pc n d st b = ws_def pc n d st i ->
              slot_free phi (bs_live_ext r K) i).
    { intros i Hib.
      apply (slot_free_from_intervals tys pc n t stf phi (bs_live_ext r K) i);
        try assumption.
      - intros Hilo Hihi.
        destruct (ws_def_interval pc n d st i Hwf Hilo Hihi)
          as [di [Hdi [Hdile Hui]]].
        rewrite <- Hib in Hdi, Hui.
        destruct Hlestf as [_ [Hdefs [Huses _]]].
        destruct (Huses _ _ Hui) as [ui' [Hui' _]].
        exists di, ui'. split; [apply Hdefs; exact Hdi | exact Hui'].
      - intros j Hj Hjlo Hjhi. destruct (Hjint j Hj Hjlo Hjhi)
          as [dj [uj [Hdj [Huj _]]]]. exists dj, uj. split; assumption.
      - intros j dj uj di ui Hj Hji Hjlo Hjhi Hilo Hihi Hdj Huj Hdi Hui.
        destruct (ws_def_interval pc n d st i Hwf Hilo Hihi)
          as [di0 [Hdi0 [Hdi0le Hui0]]].
        rewrite <- Hib in Hdi0, Hui0.
        destruct Hlestf as [Hp [Hdefs [Huses _]]].
        pose proof (Hdefs _ _ Hdi0) as Hdi'. rewrite Hdi in Hdi'.
        injection Hdi' as Hdi'. subst di0.
        destruct (Huses _ _ Hui0) as [ui1 [Hui1 Hge1]].
        rewrite Hui in Hui1. injection Hui1 as Hui1. subst ui1.
        destruct (Hjint j Hj Hjlo Hjhi) as [dj' [uj' [Hdj' [Huj' [Hd1 Hd2]]]]].
        rewrite Hdj in Hdj'. injection Hdj' as Hdj'. subst dj'.
        rewrite Huj in Huj'. injection Huj' as Huj'. subst uj'.
        assert (HdiE : di <= E).
        { destruct Hleb as [_ [Hdefs2 _]]. exact (HE i di (Hdefs2 _ _ Hdi0)). }
        split; [lia | destruct Hd2; lia]. }
    destruct b; try (solve [ cbn [apply_phi]; apply relb_plain; reflexivity ]).
    + (* local.get *) cbn [apply_phi]. apply relb_get.
    + (* local.set *) cbn [apply_phi]. apply relb_set.
      apply Hwrite. apply walk_set_eq.
    + (* local.tee *) cbn [apply_phi]. apply relb_tee.
      apply Hwrite. apply walk_tee_eq.
    + (* block *)
      rewrite walk_block_eq in Hokb, Hlestf, HAb.
      assert (Hwf0 : ws_wf pc n (ws_guard l (ws_bump st)))
        by (apply ws_guard_wf; apply ws_bump_wf; exact Hwf).
      assert (Hok0 : ws_ok (ws_guard l (ws_bump st)) = true).
      { destruct (walk_bs_le pc n (S d) (ws_guard l (ws_bump st)) l Hwf0)
          as [_ [_ [_ Ho]]]. apply Ho. exact Hokb. }
      destruct (guard_ok l (ws_bump st) Hok0) as [Hbok _].
      cbn [apply_phi]. apply relb_block.
      * apply body_ok_b_ok. exact Hbok.
      * apply (IH tys pc n t stf phi l (S d) (ws_guard l (ws_bump st))
                 A A (bs_live_ext r K)).
        -- exact Hphi.
        -- rewrite bi_size_block in Hsz. lia.
        -- exact Huni.
        -- exact Hwff.
        -- exact Hwf0.
        -- exact Hokb.
        -- exact Hlestf.
        -- apply defs_le_guard. apply defs_le_bump. exact HA.
        -- unfold ws_guard, ws_bump. destruct (body_ok_b l); cbn [ws_pos]; lia.
        -- intros Hc. discriminate Hc.
        -- exact HAb.
        -- lia.
        -- intros Hc. discriminate Hc.
        -- exact HKb.
    + (* loop: the body's own reads join K, and a write here is guarded *)
      rewrite walk_loop_eq in Hokb, Hlestf, HAb.
      assert (Hwf0 : ws_wf pc n (ws_guard l (ws_bump st)))
        by (apply ws_guard_wf; apply ws_bump_wf; exact Hwf).
      assert (Hok0 : ws_ok (ws_guard l (ws_bump st)) = true).
      { destruct (walk_bs_le pc n (S d) (ws_guard l (ws_bump st)) l Hwf0)
          as [_ [_ [_ Ho]]]. apply Ho. exact Hokb. }
      destruct (guard_ok l (ws_bump st) Hok0) as [Hbok _].
      assert (HAg : defs_le A (ws_guard l (ws_bump st)))
        by (apply defs_le_guard; apply defs_le_bump; exact HA).
      assert (Hpos0 : A <= ws_pos (ws_guard l (ws_bump st)))
        by (unfold ws_guard, ws_bump; destruct (body_ok_b l); cbn [ws_pos]; lia).
      cbn [apply_phi]. apply relb_loop.
      * apply body_ok_b_ok. exact Hbok.
      * apply (IH tys pc n t stf phi l (S d) (ws_guard l (ws_bump st))
                 A A (fun i => bs_live_b i l = true \/ bs_live_ext r K i)).
        -- exact Hphi.
        -- rewrite bi_size_loop in Hsz. lia.
        -- exact Huni.
        -- exact Hwff.
        -- exact Hwf0.
        -- exact Hokb.
        -- exact Hlestf.
        -- exact HAg.
        -- exact Hpos0.
        -- intros Hc. discriminate Hc.
        -- exact HAb.
        -- lia.
        -- intros Hc. discriminate Hc.
        -- intros j Hj Hjlo Hjhi. destruct Hj as [Hlive | Hj].
           ++ destruct ((proj2 (walk_live_start (bs_size l))) l pc n (S d)
                          (ws_guard l (ws_bump st)) j A (le_n _) Hjlo Hjhi Hwf0
                          (fun dd Hdd => HAg j dd Hdd) Hlive Hokb)
                as [dj [Hdj Hdjle]].
              destruct ((proj2 (walk_live_use (bs_size l))) l pc n (S d)
                          (ws_guard l (ws_bump st)) j (le_n _) Hjlo Hjhi Hwf0
                          Hlive Hokb) as [uj [Huj Hujge]].
              destruct Hlestf as [_ [Hdefs [Huses _]]].
              destruct (Huses _ _ Huj) as [uj' [Huj' Hle']].
              exists dj, uj'. split; [apply Hdefs; exact Hdj |].
              split; [exact Huj' | split; [exact Hdjle | lia]].
           ++ exact (HKb j Hj Hjlo Hjhi).
    + (* if *)
      rewrite walk_if_eq in Hokb, Hlestf, HAb.
      assert (Hwf0 : ws_wf pc n (ws_guard l0 (ws_guard l (ws_bump st))))
        by (apply ws_guard_wf; apply ws_guard_wf; apply ws_bump_wf; exact Hwf).
      assert (HAg : defs_le A (ws_guard l0 (ws_guard l (ws_bump st))))
        by (apply defs_le_guard; apply defs_le_guard; apply defs_le_bump;
            exact HA).
      assert (Hpos0 : A <= ws_pos (ws_guard l0 (ws_guard l (ws_bump st))))
        by (unfold ws_guard, ws_bump; destruct (body_ok_b l);
            destruct (body_ok_b l0); cbn [ws_pos]; lia).
      assert (Hwf1 : ws_wf pc n
        (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l))
        by (apply walk_bs_wf; exact Hwf0).
      assert (Hok1 : ws_ok
        (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l) = true).
      { destruct (walk_bs_le pc n (S d)
                    (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l)
                    l0 Hwf1) as [_ [_ [_ Ho]]]. apply Ho. exact Hokb. }
      assert (Hok0 : ws_ok (ws_guard l0 (ws_guard l (ws_bump st))) = true).
      { destruct (walk_bs_le pc n (S d)
                    (ws_guard l0 (ws_guard l (ws_bump st))) l Hwf0)
          as [_ [_ [_ Ho]]]. apply Ho. exact Hok1. }
      destruct (guard_ok l0 (ws_guard l (ws_bump st)) Hok0) as [Hbok2 Hok0'].
      destruct (guard_ok l (ws_bump st) Hok0') as [Hbok1 _].
      assert (Hle1 : ws_le
        (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l) stf).
      { eapply ws_le_trans; [| exact Hlestf]. apply walk_bs_le. exact Hwf1. }
      assert (HA1 : defs_le A
        (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l))
        by (apply defs_le_nonzero; [discriminate | exact HAg]).
      assert (Hpos1 : A <= ws_pos
        (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l))
        by (rewrite walk_bs_pos; lia).
      cbn [apply_phi]. apply relb_if.
      * apply body_ok_b_ok. exact Hbok1.
      * apply body_ok_b_ok. exact Hbok2.
      * apply (IH tys pc n t stf phi l (S d)
                 (ws_guard l0 (ws_guard l (ws_bump st))) A A (bs_live_ext r K));
          [ exact Hphi | rewrite bi_size_if in Hsz; lia | exact Huni | exact Hwff
          | exact Hwf0 | exact Hok1 | exact Hle1 | exact HAg | exact Hpos0
          | intros Hc; discriminate Hc | exact HA1 | lia
          | intros Hc; discriminate Hc | exact HKb ].
      * apply (IH tys pc n t stf phi l0 (S d)
                 (walk_bs pc n (S d) (ws_guard l0 (ws_guard l (ws_bump st))) l)
                 A A (bs_live_ext r K));
          [ exact Hphi | rewrite bi_size_if in Hsz; lia | exact Huni | exact Hwff
          | exact Hwf1 | exact Hokb | exact Hlestf | exact HA1 | exact Hpos1
          | intros Hc; discriminate Hc | exact HAb | lia
          | intros Hc; discriminate Hc | exact HKb ].
Qed.

(* ── 6. the pass's output is related to its input ─────────────────── *)

Lemma walk_func_eq : forall pc n body,
  walk_func pc n body
    = walk_bs pc n 0 (mk_ws 0 (M.empty nat) (M.empty nat) true) body.
Proof. reflexivity. Qed.

Lemma ws_wf_init : forall pc n,
  ws_wf pc n (mk_ws 0 (M.empty nat) (M.empty nat) true).
Proof.
  intros pc n. split; cbn [ws_defs ws_uses ws_pos];
    intros k v H; rewrite MF.empty_o in H; discriminate H.
Qed.

(* The whole function body, against the map the pass computes.  K is
   empty: a function body's continuation is the frame, which reads no
   locals of this activation. *)
Theorem coalesce_func_related : forall tys pc n t f,
  tys_uniform tys pc n t ->
  coalescable pc n f.(modfunc_body) = true ->
  rel_bs (compute_phi tys pc n f.(modfunc_body)) (fun _ => False)
         f.(modfunc_body)
         (coalesce_func tys pc n f).(modfunc_body).
Proof.
  intros tys pc n t f Huni Hc.
  unfold coalescable in Hc.
  unfold coalesce_func, apply_phi_func, compute_phi. cbn [modfunc_body].
  rewrite Hc.
  apply (rel_bs_of_walk (bs_size f.(modfunc_body)) tys pc n t
           (walk_func pc n f.(modfunc_body)) _ f.(modfunc_body) 0
           (mk_ws 0 (M.empty nat) (M.empty nat) true)
           0 (bs_size f.(modfunc_body)) (fun _ => False)).
  - reflexivity.
  - lia.
  - exact Huni.
  - rewrite walk_func_eq. apply walk_bs_wf. apply ws_wf_init.
  - apply ws_wf_init.
  - rewrite <- walk_func_eq. exact Hc.
  - rewrite <- walk_func_eq. apply ws_le_refl.
  - intros k dk H. cbn [ws_defs] in H. rewrite MF.empty_o in H. discriminate H.
  - cbn [ws_pos]. lia.
  - intros _. reflexivity.
  - intros k dk H.
    assert (Hwff : ws_wf pc n (walk_bs pc n 0
              (mk_ws 0 (M.empty nat) (M.empty nat) true) f.(modfunc_body)))
      by (apply walk_bs_wf; apply ws_wf_init).
    destruct Hwff as [Hd _]. destruct (Hd _ _ H) as [_ [_ Hle]].
    rewrite walk_bs_pos in Hle. cbn [ws_pos] in Hle. lia.
  - lia.
  - intros _. cbn [ws_pos]. lia.
  - intros j Hj. destruct Hj.
Qed.

Lemma value_type_eqb_eq : forall t t', value_type_eqb t t' = true -> t = t'.
Proof.
  intros t t' H. unfold value_type_eqb in H.
  destruct (value_type_eq_dec t t') as [He | Hne];
    [ exact He | cbn in H; discriminate H ].
Qed.

(* phi never leaves the declared slot range.  An index the walk gave an
   interval is assigned by the scan, which searches only [pc, n); any
   other index is left alone, and a rejected function gets the identity
   map.  This is what makes the coalesced body still type-check: the
   renamed local index still resolves. *)
Lemma compute_phi_range : forall tys pc n t body i,
  tys_uniform tys pc n t -> (i < n)%N ->
  (apply_phi_local (compute_phi tys pc n body) i < n)%N.
Proof.
  intros tys pc n t body i Huni Hi.
  unfold compute_phi.
  destruct (ws_ok (walk_func pc n body)) eqn:Hok.
  - assert (Hwf : ws_wf pc n (walk_func pc n body))
      by (rewrite walk_func_eq; apply walk_bs_wf; apply ws_wf_init).
    destruct (M.find i (ws_defs (walk_func pc n body))) as [d |] eqn:E.
    + destruct (phi_in_range tys pc n t _ i d Huni Hwf E) as [_ H]. exact H.
    + rewrite (phi_id_unassigned tys pc n _ i E). exact Hi.
  - rewrite apply_phi_local_empty. exact Hi.
Qed.

(* A parameter is never renamed: the scan only ever assigns indices the
   walk gave an interval, and the walk records nothing below pc. *)
Lemma compute_phi_id_below : forall tys pc n body i,
  (i < pc)%N -> apply_phi_local (compute_phi tys pc n body) i = i.
Proof.
  intros tys pc n body i Hi. unfold compute_phi.
  destruct (ws_ok (walk_func pc n body)) eqn:Hok.
  - apply phi_out_of_range.
    + rewrite walk_func_eq. apply walk_bs_wf. apply ws_wf_init.
    + intros [H1 _]. lia.
  - apply apply_phi_local_empty.
Qed.

(* Nor is anything past the last local: the scan only ever assigns slots to
   locals it has seen a def for, and ws_wf bounds those defs by n.  This is
   what makes the backward in-range component of frames_agree hold at a
   fresh activation, where both frames have exactly n locals: an index out
   of range on the source side maps to itself, hence out of range on the
   optimized side too. *)
Lemma compute_phi_id_above : forall tys pc n body i,
  (n <= i)%N -> apply_phi_local (compute_phi tys pc n body) i = i.
Proof.
  intros tys pc n body i Hi. unfold compute_phi.
  destruct (ws_ok (walk_func pc n body)) eqn:Hok.
  - apply phi_out_of_range.
    + rewrite walk_func_eq. apply walk_bs_wf. apply ws_wf_init.
    + intros [_ H2]. lia.
  - apply apply_phi_local_empty.
Qed.

(* And a non-parameter is never renamed *onto* a parameter. *)
Lemma compute_phi_lower : forall tys pc n t body i,
  tys_uniform tys pc n t -> (pc <= i)%N -> (i < n)%N ->
  (pc <= apply_phi_local (compute_phi tys pc n body) i)%N.
Proof.
  intros tys pc n t body i Huni Hlo Hhi. unfold compute_phi.
  destruct (ws_ok (walk_func pc n body)) eqn:Hok.
  - assert (Hwf : ws_wf pc n (walk_func pc n body))
      by (rewrite walk_func_eq; apply walk_bs_wf; apply ws_wf_init).
    destruct (M.find i (ws_defs (walk_func pc n body))) as [d |] eqn:E.
    + destruct (phi_in_range tys pc n t _ i d Huni Hwf E) as [H _]. exact H.
    + rewrite (phi_id_unassigned tys pc n _ i E). exact Hlo.
  - rewrite apply_phi_local_empty. exact Hlo.
Qed.

(* The slot vector is exactly as long as there are slots, in both arms of
   slot_types -- so a slot index in range always resolves. *)
Lemma slot_types_length : forall types f,
  N.of_nat (length (slot_types types f)) = func_total_locals types f.
Proof.
  intros types f. unfold slot_types, func_total_locals, func_param_count.
  destruct (lookup_N types f.(modfunc_type)) as [[ps rs] |].
  - rewrite length_app. lia.
  - lia.
Qed.

(* func_supported is a conjunction now, so split it once. *)
Lemma func_supported_i32 : forall types f,
  func_supported types f = true ->
  List.forallb slot_i32 (slot_types types f) = true.
Proof.
  intros types f H. unfold func_supported in H.
  apply Bool.andb_true_iff in H. exact (proj1 H).
Qed.

Lemma func_supported_guarded : forall types f,
  func_supported types f = true -> bs_guarded f.(modfunc_body) = true.
Proof.
  intros types f H. unfold func_supported in H.
  apply Bool.andb_true_iff in H. exact (proj2 H).
Qed.

(* func_supported's type half is precisely tys_uniform at i32: that is
   what makes the free-slot search type-blind, and hence what makes the
   counting argument in part 1 sufficient. *)
Lemma func_supported_uniform : forall types f,
  func_supported types f = true ->
  tys_uniform (slot_types types f)
              (func_param_count types f.(modfunc_type))
              (func_total_locals types f)
              (T_num T_i32).
Proof.
  intros types f Hs sl _ Hhi.
  pose proof (slot_types_length types f) as Hlen.
  unfold lookup_N.
  destruct (nth_error (slot_types types f) (N.to_nat sl)) as [x |] eqn:Ex.
  - f_equal. apply value_type_eqb_eq.
    apply (proj1 (forallb_forall slot_i32 (slot_types types f))
             (func_supported_i32 _ _ Hs) x).
    eapply nth_error_In. exact Ex.
  - exfalso. apply nth_error_None in Ex. lia.
Qed.

(* The pass, on a function its preconditions accept, produces a body
   related to the original by the relation the simulation is proved
   over.  This is the obligation coalesce_locals_correct.v leaves open:
   slot_free at every write. *)
Theorem coalesce_func_with_types_related : forall types f,
  func_supported types f = true ->
  coalescable (func_param_count types f.(modfunc_type))
              (func_total_locals types f) f.(modfunc_body) = true ->
  rel_bs (compute_phi (slot_types types f)
            (func_param_count types f.(modfunc_type))
            (func_total_locals types f) f.(modfunc_body))
         (fun _ => False)
         f.(modfunc_body)
         (coalesce_func_with_types types f).(modfunc_body).
Proof.
  intros types f Hs Hc. unfold coalesce_func_with_types.
  apply (coalesce_func_related _ _ _ (T_num T_i32)).
  - apply func_supported_uniform. exact Hs.
  - exact Hc.
Qed.

(* ── Running the two bodies ───────────────────────────────────────
   [coalesce_body_trans] runs a source body and its coalesced
   counterpart in lockstep for as long as the source runs, given
   [rel_bs] between them; the theorem above supplies exactly that for
   the map the pass computes.  Composing the two is the whole-function
   multi-step statement, and it is the first result in this development
   that is both about the pass's own output *and* about more than one
   step.

   What it still does not say: the two runs share a store, so a call
   out of this function reaches the *same*, uncoalesced, callee on both
   sides.  Lifting that is the store relation, and it is not here. *)

Section Running.

Context `{hfc : host_function_class} `{memory : BlockUpdateMemory} `{ho : host}.

Theorem coalesce_func_trans :
  forall types f hs s f_src f_opt hs' s' f_src' es',
    host_keeps_funcs ->
    store_guarded s ->
    func_supported types f = true ->
    coalescable (func_param_count types f.(modfunc_type))
                (func_total_locals types f) f.(modfunc_body) = true ->
    let phi := compute_phi (slot_types types f)
                 (func_param_count types f.(modfunc_type))
                 (func_total_locals types f) f.(modfunc_body) in
    frames_agree phi (bs_live_ext f.(modfunc_body) (fun _ => False)) f_src f_opt ->
    reduce_trans (hs, s, f_src, to_e_list f.(modfunc_body))
                 (hs', s', f_src', es') ->
    exists f_opt' es_o',
      reduce_trans (hs, s, f_opt,
                    to_e_list (coalesce_func_with_types types f).(modfunc_body))
                   (hs', s', f_opt', es_o') /\
      rel_es phi (fun _ => False) es' es_o' /\
      frames_agree phi (live_ext es' (fun _ => False)) f_src' f_opt'.
Proof.
  intros types f hs s f_src f_opt hs' s' f_src' es' Hhost Hg Hs Hc phi Hfr Htrans.
  eapply coalesce_body_trans.
  - exact Hhost.
  - exact Hg.
  - apply coalesce_func_with_types_related; assumption.
  - exact Hfr.
  - exact Htrans.
Qed.

End Running.
