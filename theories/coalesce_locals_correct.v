From Wasm Require Import datatypes datatypes_properties opsem properties.
From Stdlib Require Import List Lia.
From Wasmopt Require Import coalesce_locals toplevel_spec.

Import Bool ssreflect BinNat ListNotations.

Definition R_phi (phi : local_map) (locs locs' : list value) : Prop :=
  forall i : N, N.to_nat i < length locs ->
    nth_error locs (N.to_nat i) =
    nth_error locs' (N.to_nat (apply_phi_local phi i)).

(* The frame-level invariant carried by the simulation.  Bundling the three
   facts is what makes the multi-step closure possible: a single step must
   re-establish all of them for the successor frames, not just R_phi. *)
Definition frames_rel (phi : local_map) (f_src f_opt : frame) : Prop :=
  f_inst f_src = f_inst f_opt /\
  R_phi phi (f_locs f_src) (f_locs f_opt) /\
  (forall i : N,
     N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
     N.to_nat i < length (f_locs f_src)).

(* The opsem states its index bounds with ssreflect's leq, while the
   bounds here are Peano's <; leP is the bridge. *)
Lemma lt_to_leq : forall m n, m < n -> is_true (ssrnat.leq (S m) n).
Proof.
  intros m n H. destruct (@ssrnat.leP (S m) n) as [Hle | Hnle].
  - reflexivity.
  - exfalso. apply Hnle. exact H.
Qed.

Lemma leq_to_lt : forall m n, is_true (ssrnat.leq (S m) n) -> m < n.
Proof.
  intros m n H. destruct (@ssrnat.leP (S m) n) as [Hle | Hnle].
  - exact Hle.
  - discriminate H.
Qed.

(* set_nth at an in-range index does not change the length (it only extends
   when the index is past the end); needed to carry the length side of
   frames_rel through r_local_set. *)
Lemma length_set_nth_lt : forall (vd : value) (l : list value) n x,
  n < length l -> length (seq.set_nth vd l n x) = length l.
Proof.
  intros vd l. induction l as [|a l' IH]; intros n x Hn.
  - simpl in Hn. exfalso. inversion Hn.
  - destruct n as [|n']; simpl.
    + reflexivity.
    + f_equal. apply IH; auto with arith.
Qed.

(* ══════════════════════════════════════════════════════════════════
   Liveness-restricted agreement.
   ══════════════════════════════════════════════════════════════════

   R_phi (above) demands the two local vectors agree at *every* index.
   For a phi that merges two locals onto one slot that forces the merged
   locals to hold equal values everywhere (R_phi_forces_merged_locals_equal),
   which is true only at function entry -- so the Hset premise of the
   simulation theorems is false for exactly the phis that coalesce.

   The fix is to restrict agreement to the locals that are *live*: merged
   locals have disjoint live ranges, so at most one of them is live at any
   point and the other's stale value is unobservable.  Under that
   restriction the write case becomes provable rather than assumed --
   see R_phi_live_set. *)

Lemma nth_error_set_nth_same : forall (vd v : value) l a,
  a < length l -> nth_error (seq.set_nth vd l a v) a = Some v.
Proof.
  intros vd v l. induction l as [|x xs IH]; intros a Ha; simpl in Ha.
  - exfalso. inversion Ha.
  - destruct a as [|a']; simpl.
    + reflexivity.
    + apply IH. auto with arith.
Qed.

Lemma nth_error_set_nth_other : forall (vd v : value) l a b,
  a < length l -> a <> b -> nth_error (seq.set_nth vd l a v) b = nth_error l b.
Proof.
  intros vd v l. induction l as [|x xs IH]; intros a b Ha Hab; simpl in Ha.
  - exfalso. inversion Ha.
  - destruct a as [|a']; destruct b as [|b']; simpl.
    + exfalso. apply Hab. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH; [ auto with arith | intro Heq; apply Hab; rewrite Heq; reflexivity ].
Qed.

(* Agreement restricted to a live set L. *)
Definition R_phi_live (phi : local_map) (L : N -> Prop) (locs locs' : list value) : Prop :=
  forall i : N, N.to_nat i < length locs -> L i ->
    nth_error locs (N.to_nat i) =
    nth_error locs' (N.to_nat (apply_phi_local phi i)).

(* R_phi is the special case where everything is live, so the old (false for
   merging phi) situation is recovered exactly by taking L := fun _ => True. *)
Lemma R_phi_live_all : forall phi locs locs',
  R_phi phi locs locs' <-> R_phi_live phi (fun _ => True) locs locs'.
Proof.
  intros phi locs locs'. split.
  - intros H i Hi _. exact (H i Hi).
  - intros H i Hi. exact (H i Hi I).
Qed.

(* The corrected Hset.  Under the unrestricted R_phi this statement is FALSE
   for a merging phi; restricted to live locals it is provable, given the
   condition the coalescing is meant to guarantee: after writing i', no other
   local sharing i''s slot is still live. *)
Lemma R_phi_live_set : forall phi (L L' : N -> Prop) locs locs' (v vd : value) (i' : N),
  (forall j, L' j -> j <> i' -> apply_phi_local phi j <> apply_phi_local phi i') ->
  (forall j, L' j -> j <> i' -> L j) ->
  N.to_nat i' < length locs ->
  N.to_nat (apply_phi_local phi i') < length locs' ->
  R_phi_live phi L locs locs' ->
  R_phi_live phi L'
    (seq.set_nth vd locs  (N.to_nat i') v)
    (seq.set_nth vd locs' (N.to_nat (apply_phi_local phi i')) v).
Proof.
  intros phi L L' locs locs' v vd i' Hkill Hsub Hi' Hphi' HR.
  intros j Hj HL'j.
  destruct (N.eq_dec j i') as [Heq | Hne].
  - subst j.
    rewrite (nth_error_set_nth_same vd v locs (N.to_nat i') Hi').
    rewrite (nth_error_set_nth_same vd v locs' _ Hphi').
    reflexivity.
  - assert (Hnn : N.to_nat i' <> N.to_nat j).
    { intro Habs. apply Hne. symmetry. apply Nnat.N2Nat.inj. exact Habs. }
    rewrite (nth_error_set_nth_other vd v locs (N.to_nat i') (N.to_nat j) Hi' Hnn).
    assert (Hslot : N.to_nat (apply_phi_local phi i') <> N.to_nat (apply_phi_local phi j)).
    { intro Habs. apply (Hkill j HL'j Hne). symmetry. apply Nnat.N2Nat.inj. exact Habs. }
    rewrite (nth_error_set_nth_other vd v locs' _ _ Hphi' Hslot).
    apply HR.
    + rewrite (length_set_nth_lt vd locs (N.to_nat i') v Hi') in Hj. exact Hj.
    + exact (Hsub j HL'j Hne).
Qed.

(* ── The pass's own phi ─────────────────────────────────────────── *)

Lemma apply_phi_local_empty : forall i, apply_phi_local empty i = i.
Proof. intros i. reflexivity. Qed.

Lemma apply_phi_empty_id : forall b, apply_phi empty b = b.
Proof.
  fix IH 1. intros b.
  destruct b; simpl; try reflexivity.
  all: try (f_equal;
            match goal with
            | |- List.map _ ?l = ?l =>
                induction l as [|x xs Hxs]; simpl;
                [ reflexivity | rewrite IH; rewrite Hxs; reflexivity ]
            end).
Qed.

Lemma map_apply_phi_empty_id : forall l, List.map (apply_phi empty) l = l.
Proof.
  intros l. induction l as [|x xs Hxs]; simpl.
  - reflexivity.
  - rewrite apply_phi_empty_id. rewrite Hxs. reflexivity.
Qed.

Lemma compute_phi_rejected : forall tys pc n body,
  coalescable pc n body = false -> compute_phi tys pc n body = empty.
Proof.
  intros tys pc n body H. unfold compute_phi, coalescable in *.
  destruct (ws_ok (walk_func pc n body)); [discriminate H | reflexivity].
Qed.

(* ── The truncation bound ─────────────────────────────────────────
   [slot_bound pc n phi] is one past the largest slot phi can produce
   from a source index in [pc, n), floored at pc.  Three facts are
   wanted downstream and all three are folds: it dominates the image
   (so the renamed body fits the shortened frame), it is dominated by
   any bound on the image (so the truncation never lengthens the local
   vector), and on the empty map it is exactly n (so a rejected
   function keeps every local it declared). *)

Lemma slot_bound_aux_ge : forall len phi k j,
  (k <= j)%N -> (j < k + N.of_nat len)%N ->
  (apply_phi_local phi j < slot_bound_aux phi k len)%N.
Proof.
  induction len as [| l IH]; intros phi k j H1 H2; cbn [slot_bound_aux].
  - lia.
  - destruct (N.eq_dec k j) as [He | Hne].
    + subst j. lia.
    + specialize (IH phi (N.succ k) j ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma slot_bound_aux_le : forall len phi k B,
  (forall j, (k <= j)%N -> (j < k + N.of_nat len)%N ->
             (apply_phi_local phi j < B)%N) ->
  (slot_bound_aux phi k len <= B)%N.
Proof.
  induction len as [| l IH]; intros phi k B H; cbn [slot_bound_aux].
  - lia.
  - assert (Hk : (apply_phi_local phi k < B)%N) by (apply H; lia).
    assert (Hrest : (slot_bound_aux phi (N.succ k) l <= B)%N)
      by (apply IH; intros j Hj1 Hj2; apply H; lia).
    lia.
Qed.

Lemma slot_bound_aux_empty : forall len k,
  N.max k (slot_bound_aux empty k len) = (k + N.of_nat len)%N.
Proof.
  induction len as [| l IH]; intros k; cbn [slot_bound_aux].
  - lia.
  - rewrite apply_phi_local_empty. specialize (IH (N.succ k)). lia.
Qed.

Lemma slot_bound_ge : forall pc n phi, (pc <= slot_bound pc n phi)%N.
Proof. intros pc n phi. unfold slot_bound. lia. Qed.

(* Every slot the renamed body can name is below the bound. *)
Lemma slot_bound_hit : forall pc n phi j,
  (pc <= j)%N -> (j < n)%N ->
  (apply_phi_local phi j < slot_bound pc n phi)%N.
Proof.
  intros pc n phi j H1 H2. unfold slot_bound.
  pose proof (slot_bound_aux_ge (N.to_nat n - N.to_nat pc) phi pc j H1
                ltac:(lia)) as H. lia.
Qed.

(* And the bound never exceeds a bound already known for the image, so
   the kept prefix is a prefix. *)
Lemma slot_bound_le : forall pc n phi,
  (pc <= n)%N ->
  (forall j, (pc <= j)%N -> (j < n)%N -> (apply_phi_local phi j < n)%N) ->
  (slot_bound pc n phi <= n)%N.
Proof.
  intros pc n phi Hpc H. unfold slot_bound.
  assert (Haux : (slot_bound_aux phi pc (N.to_nat n - N.to_nat pc) <= n)%N)
    by (apply slot_bound_aux_le; intros j Hj1 Hj2; apply H; lia).
  lia.
Qed.

Lemma slot_bound_empty : forall pc n, (pc <= n)%N -> slot_bound pc n empty = n.
Proof.
  intros pc n H. unfold slot_bound. rewrite slot_bound_aux_empty. lia.
Qed.

(* When the guard rejects a function, the pass is the identity on it:
   the map is empty, so no index is renamed and the bound is n, which
   keeps every declared local.  The only hypothesis is the arity
   discipline the pass is called under -- n counts the parameters plus
   the declared locals -- without which "keep n - pc of them" would not
   be the whole vector.  This is what makes a rejected input (a local
   read before it is written, or a body that both branches and writes)
   safe. *)
Theorem coalesce_func_rejected_id : forall tys pc n f,
  n = (pc + N.of_nat (length f.(modfunc_locals)))%N ->
  coalescable pc n (modfunc_body f) = false -> coalesce_func tys pc n f = f.
Proof.
  intros tys pc n f Hn H. unfold coalesce_func.
  rewrite (compute_phi_rejected tys pc n (modfunc_body f) H).
  rewrite map_apply_phi_empty_id.
  rewrite (slot_bound_empty pc n ltac:(lia)).
  replace (N.to_nat (n - pc)) with (length f.(modfunc_locals)) by lia.
  rewrite firstn_all.
  destruct f; reflexivity.
Qed.

(* The same one level up, and for the same reason: a module the
   preconditions reject is returned untouched, so the top-level statement
   for it is reflexivity and needs no relation at all.  This is what keeps
   the unsupported cases -- a start section, or a slot that is not i32 --
   out of the simulation entirely. *)
Theorem coalesce_module_unsupported_id : forall m,
  module_supported m = false -> coalesce_module m = m.
Proof.
  intros m H. unfold coalesce_module. rewrite H. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════
   Liveness: which locals the remaining code can still *read*.
   ══════════════════════════════════════════════════════════════════

   The live set that R_phi_live is keyed on need not be supplied
   separately: in a small-step semantics the instruction list *is* the
   whole remaining continuation of the current activation, so "still
   readable" is a structural property of it.  Recursion stops at
   AI_frame, which is a different activation with its own locals.

   Crucially this is read-*before*-write, not "mentions a local.get
   somewhere": a write to i makes the earlier value unobservable, so it
   must end i's live range.  Without the kill, a local would stay live
   across its own redefinition and the write case below (R_phi_live_set)
   would be unusable.

   The approximation is one-sided in the safe direction: block/loop/if
   are treated as *not* killing (a branch may skip the write), so the
   live set is an over-approximation, which is what soundness needs. *)

(* bi_kills / bi_live / bs_live_b / bs_kills_b now live in
   coalesce_locals.v: the walk itself consults them. *)

(* A trap kills everything.  Nothing after it runs, so no read of any local
   can follow -- which is what makes rs_trap work: that rule throws the
   whole context away, including any local.set pending in it, so a local
   the context was going to kill would otherwise come back to life with no
   way to re-establish agreement for it.  With the trap killing, the live
   set after a trap is empty and there is nothing to re-establish. *)
Fixpoint ai_kills (i : N) (e : administrative_instruction) {struct e} : bool :=
  let fix esk (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_kills i e' || esk rest
    end in
  match e with
  | AI_basic b => bi_kills i b
  | AI_trap => true
  | AI_label _ _ b => esk b
  | _ => false                          (* AI_frame: a different activation *)
  end.

Fixpoint es_kills_b (i : N) (es : list administrative_instruction) : bool :=
  match es with
  | [] => false
  | e :: rest => ai_kills i e || es_kills_b i rest
  end.

Lemma ai_kills_label : forall i n a b,
  ai_kills i (AI_label n a b) = es_kills_b i b.
Proof.
  intros i n a b.
  assert (H : forall l, (fix esk (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_kills i e' || esk rest
    end) l = es_kills_b i l).
  { induction l as [|x xs IHx]; simpl; [reflexivity | rewrite IHx; reflexivity ]. }
  simpl. apply H.
Qed.

(* A label's branch continuation only runs if the body does not kill first,
   exactly as for a cons cell.  Being precise here is what makes the live
   set of a filled context *equal* the live set of its hole, rather than
   merely contain it -- and that equality is what r_label needs, since it
   has to hand the invariant down to the hole and get it back afterwards. *)
Fixpoint ai_live (i : N) (e : administrative_instruction) {struct e} : bool :=
  let fix esl (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_live i e' || (negb (ai_kills i e') && esl rest)
    end in
  match e with
  | AI_basic b => bi_live i b
  | AI_label _ a b => esl b || (negb (es_kills_b i b) && esl a)
  | _ => false
  end.

Fixpoint es_live_b (i : N) (es : list administrative_instruction) : bool :=
  match es with
  | [] => false
  | e :: rest => ai_live i e || (negb (ai_kills i e) && es_live_b i rest)
  end.

Lemma ai_live_label : forall i n a b,
  ai_live i (AI_label n a b) =
  es_live_b i b || (negb (es_kills_b i b) && es_live_b i a).
Proof.
  intros i n a b.
  assert (H : forall l, (fix esl (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_live i e' || (negb (ai_kills i e') && esl rest)
    end) l = es_live_b i l).
  { induction l as [|x xs IHx]; simpl; [reflexivity | rewrite IHx; reflexivity ]. }
  simpl. rewrite (H a). rewrite (H b). reflexivity.
Qed.

(* The live set of [es followed by a continuation whose live set is K].
   Threading K this way rather than taking a plain union is what makes the
   append and split lemmas exact inverses: a kill inside es shadows a read
   in the continuation, which a union would lose.  live_ext_app below is
   the associativity that this buys. *)
Definition bs_live_ext (bs : list basic_instruction) (K : N -> Prop) (i : N) : Prop :=
  bs_live_b i bs = true \/ (bs_kills_b i bs = false /\ K i).

Definition live_ext (es : list administrative_instruction) (K : N -> Prop) (i : N) : Prop :=
  es_live_b i es = true \/ (es_kills_b i es = false /\ K i).

Definition es_live (es : list administrative_instruction) (i : N) : Prop :=
  es_live_b i es = true.

(* The obligation a write carries: nothing else the continuation can still
   read shares the slot being written.  This is the register-allocation
   side condition, and it is exactly what R_phi_live_set consumes. *)
Definition slot_free (phi : local_map) (L : N -> Prop) (i' : N) : Prop :=
  forall j, L j -> j <> i' -> apply_phi_local phi j <> apply_phi_local phi i'.

(* ── Where writes may occur ────────────────────────────────────────
   A local.set/tee under structured control is permitted, but only in a
   body that cannot branch: that is what the pass checks on the way in
   (coalesce_locals.v, body_ok_b) and what the relation below records.
   It is also what makes the r_label bookkeeping close -- a body whose
   kills really happen leaves the live set of a filled context equal to
   the live set of the hole under lh_K (live_ext_lfill).

   The pass carries a second, independent restriction that the relation
   does not see: a guarded def opens its live interval at function entry,
   because it need not dominate the uses the source-order interval model
   assumes it does.  That is an allocation question, not a semantic one,
   and it shows up here only as slot_free.

   Without it the relation is unsound, not merely imprecise.  Take a loop
   whose body is [get 2; set 1; br 0; set 2] with phi 1 = phi 2: the write
   to 1 is permitted because es_kills_b sees the later set 2 and treats 2
   as dead, but br 0 jumps back to get 2 before set 2 ever runs, so the
   second iteration reads the slot holding local 1's value. *)

(* bi_writes / bs_writes live in coalesce_locals.v: the pass runs the same
   check, and one definition keeps the two from drifting apart. *)

Lemma bi_writes_block : forall bt bs, bi_writes (BI_block bt bs) = bs_writes bs.
Proof.
  intros bt bs. induction bs as [|b rest IH]; simpl; [reflexivity |].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma bi_writes_loop : forall bt bs, bi_writes (BI_loop bt bs) = bs_writes bs.
Proof.
  intros bt bs. induction bs as [|b rest IH]; simpl; [reflexivity |].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma bi_writes_if : forall bt b1 b2,
  bi_writes (BI_if bt b1 b2) = bs_writes b1 || bs_writes b2.
Proof.
  intros bt b1 b2.
  rewrite <- (bi_writes_block bt b1). rewrite <- (bi_writes_block bt b2).
  reflexivity.
Qed.

Fixpoint ai_writes (e : administrative_instruction) {struct e} : bool :=
  let fix esw (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_writes e' || esw rest
    end in
  match e with
  | AI_basic b => bi_writes b
  | AI_label _ a b => esw a || esw b
  | _ => false                          (* AI_frame: a different activation *)
  end.

Fixpoint es_writes (es : list administrative_instruction) : bool :=
  match es with
  | [] => false
  | e :: rest => ai_writes e || es_writes rest
  end.

Lemma ai_writes_label : forall n a b,
  ai_writes (AI_label n a b) = es_writes a || es_writes b.
Proof.
  intros n a b.
  assert (H : forall l, (fix esw (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_writes e' || esw rest
    end) l = es_writes l).
  { induction l as [|x xs IHx]; simpl; [reflexivity | rewrite IHx; reflexivity ]. }
  simpl. rewrite (H a). rewrite (H b). reflexivity.
Qed.

Lemma es_writes_app : forall es1 es2,
  es_writes (es1 ++ es2) = es_writes es1 || es_writes es2.
Proof.
  intros es1. induction es1 as [|e es1' IH]; intros es2; simpl.
  - reflexivity.
  - rewrite IH. apply Bool.orb_assoc.
Qed.

(* A write is the only way for a *basic* instruction to kill.  There is no
   such lemma at the administrative level any more: a trap kills without
   writing, which is deliberate (see ai_kills). *)
Lemma bi_kills_writes : forall i b, bi_writes b = false -> bi_kills i b = false.
Proof. intros i b H. destruct b; simpl in *; try reflexivity; discriminate H. Qed.

Lemma bs_writes_to_e_list : forall bs, es_writes (to_e_list bs) = bs_writes bs.
Proof.
  intros bs. induction bs as [|b bs' IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(* ── Where branches occur ─────────────────────────────────────────
   A branch is the only way for control to leave a structured body early,
   and so the only way for a body's kills to be skipped -- which is what
   makes the liveness of a label body inexact.  A body with no branch runs
   to completion, so its kills really happen and rs_br cannot fire on it:
   that is the cheap disjunct of label_ok, and it is what lets a block or
   an if body write.

   Stated as "contains a branch" rather than "is branch-free" so that the
   whole development mirrors bi_writes/es_writes, down to the orb
   rewrites in the tactic below.  Branch-freedom is [es_br es = false].

   BI_return and BI_return_call are not branches for this purpose: they
   leave the activation entirely, so no later read of these locals can
   run, and a kill they skip cannot matter. *)
(* bi_br / bs_br live in coalesce_locals.v, next to bi_writes and for the
   same reason. *)

Lemma bi_br_block : forall bt bs, bi_br (BI_block bt bs) = bs_br bs.
Proof.
  intros bt bs. induction bs as [|b rest IH]; simpl; [reflexivity |].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma bi_br_loop : forall bt bs, bi_br (BI_loop bt bs) = bs_br bs.
Proof.
  intros bt bs. induction bs as [|b rest IH]; simpl; [reflexivity |].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma bi_br_if : forall bt b1 b2,
  bi_br (BI_if bt b1 b2) = bs_br b1 || bs_br b2.
Proof.
  intros bt b1 b2.
  rewrite <- (bi_br_block bt b1). rewrite <- (bi_br_block bt b2).
  reflexivity.
Qed.

Fixpoint ai_br (e : administrative_instruction) {struct e} : bool :=
  let fix esb (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_br e' || esb rest
    end in
  match e with
  | AI_basic b => bi_br b
  | AI_label _ a b => esb a || esb b
  | _ => false                          (* AI_frame: a different activation *)
  end.

Fixpoint es_br (es : list administrative_instruction) : bool :=
  match es with
  | [] => false
  | e :: rest => ai_br e || es_br rest
  end.

Lemma ai_br_label : forall n a b,
  ai_br (AI_label n a b) = es_br a || es_br b.
Proof.
  intros n a b.
  assert (H : forall l, (fix esb (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_br e' || esb rest
    end) l = es_br l).
  { induction l as [|x xs IHx]; simpl; [reflexivity | rewrite IHx; reflexivity ]. }
  simpl. rewrite (H a). rewrite (H b). reflexivity.
Qed.

Lemma es_br_app : forall es1 es2,
  es_br (es1 ++ es2) = es_br es1 || es_br es2.
Proof.
  intros es1. induction es1 as [|e es1' IH]; intros es2; simpl.
  - reflexivity.
  - rewrite IH. apply Bool.orb_assoc.
Qed.

Lemma bs_br_to_e_list : forall bs, es_br (to_e_list bs) = bs_br bs.
Proof.
  intros bs. induction bs as [|b bs' IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(* ── Hazards ──────────────────────────────────────────────────────
   A list is hazard-free when, in the current activation, it can neither
   write a local nor trap: no local.set/tee anywhere -- nested inside
   blocks and inside label continuations included -- and no trap.

   This is what label_ok asks of a label body, rather than the weaker
   kill-freedom it really needs, because hazard-freedom survives a step
   and kill-freedom does not: a write nested in a block does not kill
   (a branch may skip the block), but r_block turns that block into a
   label whose body does kill. *)
Fixpoint ai_hazard (e : administrative_instruction) {struct e} : bool :=
  let fix esh (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_hazard e' || esh rest
    end in
  match e with
  | AI_basic b => bi_writes b
  | AI_trap => true
  | AI_label _ a b => esh a || esh b
  | _ => false                          (* AI_frame: a different activation *)
  end.

Fixpoint es_hazard (es : list administrative_instruction) : bool :=
  match es with
  | [] => false
  | e :: rest => ai_hazard e || es_hazard rest
  end.

Lemma ai_hazard_label : forall n a b,
  ai_hazard (AI_label n a b) = es_hazard a || es_hazard b.
Proof.
  intros n a b.
  assert (H : forall l, (fix esh (es : list administrative_instruction) : bool :=
    match es with
    | [] => false
    | e' :: rest => ai_hazard e' || esh rest
    end) l = es_hazard l).
  { induction l as [|x xs IHx]; simpl; [reflexivity | rewrite IHx; reflexivity ]. }
  simpl. rewrite (H a). rewrite (H b). reflexivity.
Qed.

Lemma es_hazard_app : forall es1 es2,
  es_hazard (es1 ++ es2) = es_hazard es1 || es_hazard es2.
Proof.
  intros es1. induction es1 as [|e es1' IH]; intros es2; simpl.
  - reflexivity.
  - rewrite IH. apply Bool.orb_assoc.
Qed.

(* The opsem states its concatenations with seq.cat, which is convertible
   with ++ but does not match it syntactically for rewriting. *)
Lemma es_hazard_cat : forall es1 es2,
  es_hazard (seq.cat es1 es2) = es_hazard es1 || es_hazard es2.
Proof. exact es_hazard_app. Qed.

Lemma ai_hazard_v_to_e : forall v, ai_hazard (v_to_e v) = false.
Proof.
  intros v. destruct v as [n | vv | r]; [reflexivity | reflexivity |].
  destruct r; reflexivity.
Qed.

Lemma es_hazard_const : forall es,
  is_true (const_list es) -> es_hazard es = false.
Proof.
  intros es. induction es as [|e es' IH]; intros H; [reflexivity |].
  rewrite const_list_cons in H. apply Bool.andb_true_iff in H.
  destruct H as [H1 H2]. simpl. rewrite (IH H2). rewrite Bool.orb_false_r.
  destruct (is_const_exists H1) as [v Hv]. subst e. apply ai_hazard_v_to_e.
Qed.

Lemma es_hazard_to_e_list : forall bs, es_hazard (to_e_list bs) = bs_writes bs.
Proof.
  intros bs. induction bs as [|b bs' IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(* Hazard-freedom is the stronger notion: it forbids the writes that kill
   directly, the trap that kills everything, and the writes nested under
   structured control that do not kill yet but would after a step. *)
Lemma es_hazard_kills : forall i es,
  es_hazard es = false -> es_kills_b i es = false.
Proof.
  (* The instruction-level statement first: the recursion has to go
     through a label's body, which is not a structural subterm of the
     enclosing list, so this is the library's nested scheme rather than
     a plain list induction. *)
  assert (Hai : forall e i, ai_hazard e = false -> ai_kills i e = false).
  { intros e. induction e as
      [ bb | | fa | ea | fa2 | fa3 | nl la Fa lb Fb | nf ff lf Ff ]
    using administrative_instruction_ind';
    intros i H; try reflexivity.
    - apply bi_kills_writes. exact H.
    - discriminate H.
    - rewrite ai_kills_label. rewrite ai_hazard_label in H.
      apply Bool.orb_false_iff in H. destruct H as [_ Hb].
      clear Fa. revert Hb. induction Fb as [| e' l' He' Hl' IH];
      intros Hb; [ reflexivity |].
      cbn [es_hazard] in Hb. cbn [es_kills_b].
      apply Bool.orb_false_iff in Hb. destruct Hb as [Hb1 Hb2].
      rewrite (He' i Hb1). exact (IH Hb2). }
  intros i es. induction es as [| e es' IH]; intros H; [ reflexivity |].
  cbn [es_hazard] in H. cbn [es_kills_b].
  apply Bool.orb_false_iff in H. destruct H as [H1 H2].
  rewrite (Hai e i H1). exact (IH H2).
Qed.

(* ══════════════════════════════════════════════════════════════════
   The frame-aware configuration relation.
   ══════════════════════════════════════════════════════════════════

   apply_phi_es is a *function* that stops at AI_frame, which was right
   for relating one function body but says nothing about a whole-program
   run -- and a whole-program run is a nest of frames.  The replacement is
   a relation, with phi an index rather than a parameter so that each
   AI_frame can carry the map of its own function together with the
   agreement between that activation's two frames.

   The well-formedness of the rename is carried by the relation itself
   (relb_set / relb_tee) rather than by a separate predicate.  It is stated
   inductively for the same reason the liveness functions needed the local
   fix: a Fixpoint alternating between basic_instruction and lists of them
   is not accepted, whereas an inductive gives sub-derivations and hence
   usable induction hypotheses. *)

Definition plain_b (b : basic_instruction) : bool :=
  match b with
  | BI_local_get _ | BI_local_set _ | BI_local_tee _
  | BI_block _ _ | BI_loop _ _ | BI_if _ _ _ => false
  | _ => true
  end.

(* What a structured body must satisfy for its label to admit rs_br.  See
   the constructors below for why these are the two ways out. *)
Definition body_ok (bs : list basic_instruction) : Prop :=
  bs_br bs = false \/ bs_writes bs = false.

(* body_ok_b, its decidable form, is in coalesce_locals.v: it is literally
   the guard walk_instr applies on entering a structured body. *)

Lemma body_ok_b_ok : forall bs, body_ok_b bs = true -> body_ok bs.
Proof.
  intros bs H. unfold body_ok_b in H. apply Bool.orb_true_iff in H.
  destruct H as [H | H]; apply Bool.negb_true_iff in H;
  [ left | right ]; exact H.
Qed.

Lemma body_ok_nowrite : forall bs, bs_writes bs = false -> body_ok bs.
Proof. intros bs H. right. exact H. Qed.

Lemma body_ok_nobr : forall bs, bs_br bs = false -> body_ok bs.
Proof. intros bs H. left. exact H. Qed.

Inductive rel_b : local_map -> (N -> Prop) -> basic_instruction -> basic_instruction -> Prop :=
| relb_plain : forall phi K b, plain_b b = true -> rel_b phi K b b
| relb_get : forall phi K i,
    rel_b phi K (BI_local_get i) (BI_local_get (apply_phi_local phi i))
| relb_set : forall phi K i, slot_free phi K i ->
    rel_b phi K (BI_local_set i) (BI_local_set (apply_phi_local phi i))
| relb_tee : forall phi K i, slot_free phi K i ->
    rel_b phi K (BI_local_tee i) (BI_local_tee (apply_phi_local phi i))
(* The condition on a structured body, and the reason label_ok has the
   shape it does.  A write inside a body is only safe if the body's kills
   really happen, and the one thing that can skip them is a branch out of
   (or back to the top of) the body: it jumps over a kill the liveness
   already counted.  So the body must have no branch, or no write.

   Branch-freedom is the disjunct that matters in practice -- it lets a
   block or an if body write, which is where most writes are -- and it is
   the one that survives a step untouched, since a trap landing in the
   body is not a branch.  Write-freedom covers the rest: a loop whose body
   branches back must not write, because the back edge re-runs the body
   and the branch continuation (the loop itself) reads what the body
   reads.  The pass's nesting guard enforces one of the two. *)
| relb_block : forall phi K bt bs bs_o,
    body_ok bs ->
    rel_bs phi K bs bs_o ->
    rel_b phi K (BI_block bt bs) (BI_block bt bs_o)
| relb_loop : forall phi K bt bs bs_o,
    body_ok bs ->
    rel_bs phi (fun i => bs_live_b i bs = true \/ K i) bs bs_o ->
    rel_b phi K (BI_loop bt bs) (BI_loop bt bs_o)
| relb_if : forall phi K bt b1 b1_o b2 b2_o,
    body_ok b1 -> body_ok b2 ->
    rel_bs phi K b1 b1_o -> rel_bs phi K b2 b2_o ->
    rel_b phi K (BI_if bt b1 b2) (BI_if bt b1_o b2_o)
with rel_bs : local_map -> (N -> Prop) -> list basic_instruction -> list basic_instruction -> Prop :=
| relbs_nil : forall phi K, rel_bs phi K nil nil
| relbs_cons : forall phi K b b_o bs bs_o,
    rel_b phi (bs_live_ext bs K) b b_o -> rel_bs phi K bs bs_o ->
    rel_bs phi K (b :: bs) (b_o :: bs_o).

(* The condition under which a label's live set decomposes exactly into
   its body's.  The label contributes its branch continuation's reads
   ungated, while the body's own view gates them behind the body's kills;
   the two agree as soon as one of the following holds.

   Both disjuncts are needed.  Blocks, ifs, and the label wrapping a whole
   function body have an empty branch continuation, so the first holds and
   the body may write freely -- which is essential, since that is where all
   the writes are.  A loop's continuation is the loop itself, so its reads
   are real, and there the body must not write; the pass's nesting-depth
   guard already rejects those. *)
(* A configuration that has already trapped: the trap is the redex and
   everything to its left is values, at every nesting level.  This is the
   only way a trap can occur in a reachable state, since lfill's prefix is
   always a value list. *)
Definition trapping (es : list administrative_instruction) : Prop :=
  exists k (lh : lholed k), es = lfill lh [AI_trap].

(* Either the body performs no kill that could shadow the continuation, or
   the label's live-out is empty and there is nothing to shadow.  What the
   first disjunct really needs is kill-freedom; it asks for the stronger
   hazard-freedom because kill-freedom is not preserved by a step -- a
   write nested in a block does not kill, and r_block turns that block
   into a label whose body does.  The trapping escape is needed because a
   step can drop a trap into a body, and a trap kills. *)
Definition label_ok (a b : list administrative_instruction) (K : N -> Prop) : Prop :=
  es_br b = false
  \/ es_hazard b = false
  \/ ((forall i, es_live_b i a = false) /\ (forall i, ~ K i))
  \/ trapping b.

(* The cheap disjunct, and the one that carries block and if bodies: with
   no branch in the body, rs_br simply cannot fire, so there is no
   obligation to discharge and the body may write freely.  It is preserved
   by a step (reduce_nobr) and, unlike hazard-freedom, it is untouched by
   a trap landing in the body -- which is why the constructors for blocks
   and ifs need no write condition at all. *)
Lemma label_ok_nobr : forall a b K,
  es_br b = false -> label_ok a b K.
Proof. intros a b K H. left. exact H. Qed.

Lemma label_ok_nohazard : forall a b K,
  es_hazard b = false -> label_ok a b K.
Proof. intros a b K H. right. left. exact H. Qed.

Lemma label_ok_dead : forall a b K,
  (forall i, es_live_b i a = false) -> (forall i, ~ K i) -> label_ok a b K.
Proof.
  intros a b K Ha HK. right. right. left. split; [ exact Ha | exact HK ].
Qed.

(* Agreement between two frames of the *same* activation, restricted to a
   live set. *)
(* The in-range component is not decoration: at a local.set the target must
   have the slot phi j, and j is *dead* at that point (its own write kills
   it), so R_phi_live says nothing about it.  Lengths never change --
   set_nth at an in-range index preserves them -- so carrying this costs
   nothing to maintain.

   The *converse* in-range component is what the backward simulation needs.
   There the optimized side takes the step, so the index that is known to be
   in range is the slot, and the source index -- which the relation only
   pins down up to [apply_phi_local phi i = j] -- has to be shown in range
   before the source can take the matching step at all.  It costs nothing to
   maintain for the same reason, and it holds where the agreement is built:
   at a fresh activation phi is the identity outside [0, n) (phi_out_of_range),
   and the two frames there have the same length. *)
Definition frames_agree (phi : local_map) (L : N -> Prop) (f f_opt : frame) : Prop :=
  f_inst f = f_inst f_opt /\
  (forall i, N.to_nat i < length (f_locs f) ->
             N.to_nat (apply_phi_local phi i) < length (f_locs f_opt)) /\
  (forall i, N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
             N.to_nat i < length (f_locs f)) /\
  R_phi_live phi L (f_locs f) (f_locs f_opt).

(* A fresh activation is related to itself under the identity map: this is
   what r_invoke_native installs, since the callee's body has not been
   renamed (the pass runs per function, and the callee is optimized
   separately). *)
Lemma frames_agree_empty_refl : forall L f, frames_agree empty L f f.
Proof.
  intros L f. split; [reflexivity | split; [| split]].
  - intros i Hi. rewrite apply_phi_local_empty. exact Hi.
  - intros i Hi. rewrite apply_phi_local_empty in Hi. exact Hi.
  - intros i Hi HL. rewrite apply_phi_local_empty. reflexivity.
Qed.

Lemma frames_agree_mono : forall phi L L' f f_o,
  (forall i, L' i -> L i) -> frames_agree phi L f f_o -> frames_agree phi L' f f_o.
Proof.
  intros phi L L' f f_o Hsub [H1 [H2 [H2' H3]]].
  split; [exact H1 | split; [exact H2 | split; [exact H2' |]]].
  intros i Hi HL'. exact (H3 i Hi (Hsub i HL')).
Qed.

Inductive rel_e : local_map -> (N -> Prop) -> administrative_instruction -> administrative_instruction -> Prop :=
| rel_basic : forall phi K b b_o,
    rel_b phi K b b_o -> rel_e phi K (AI_basic b) (AI_basic b_o)
| rel_trap : forall phi K, rel_e phi K AI_trap AI_trap
| rel_ref : forall phi K a, rel_e phi K (AI_ref a) (AI_ref a)
| rel_ref_extern : forall phi K e, rel_e phi K (AI_ref_extern e) (AI_ref_extern e)
| rel_invoke : forall phi K a, rel_e phi K (AI_invoke a) (AI_invoke a)
| rel_return_invoke : forall phi K a, rel_e phi K (AI_return_invoke a) (AI_return_invoke a)
(* The body's live-out is the label's own live-out K together with what the
   branch continuation a reads, since a br transfers control to a. *)
| rel_label : forall phi K n a a_o b b_o,
    label_ok a b K ->
    rel_es phi K a a_o ->
    rel_es phi (fun i => es_live_b i a = true \/ K i) b b_o ->
    rel_e phi K (AI_label n a b) (AI_label n a_o b_o)
(* A frame carries its own map psi, its own frame agreement, and an empty
   context: nothing outside an activation can read its locals. *)
| rel_frame : forall phi K psi n f f_o es es_o,
    frames_agree psi (es_live es) f f_o ->
    rel_es psi (fun _ => False) es es_o ->
    rel_e phi K (AI_frame n f es) (AI_frame n f_o es_o)
with rel_es : local_map -> (N -> Prop) -> list administrative_instruction -> list administrative_instruction -> Prop :=
| rel_nil : forall phi K, rel_es phi K nil nil
| rel_cons : forall phi K e e_o es es_o,
    rel_e phi (live_ext es K) e e_o ->
    rel_es phi K es es_o ->
    rel_es phi K (e :: es) (e_o :: es_o).

(* ── Weakening: a smaller context imposes weaker obligations ──────── *)

Lemma label_ok_weaken : forall a b K K',
  (forall i, K' i -> K i) -> label_ok a b K -> label_ok a b K'.
Proof.
  intros a b K K' Hsub [Hb | [Hh | [[Hl HK] | Ht]]];
  [ left; exact Hb | right; left; exact Hh | | right; right; right; exact Ht ].
  right. right. left. split;
  [ exact Hl | intros i HK'; apply (HK i); exact (Hsub i HK') ].
Qed.

Lemma slot_free_weaken : forall phi K K' i',
  (forall i, K' i -> K i) -> slot_free phi K i' -> slot_free phi K' i'.
Proof. intros phi K K' i' Hsub H j Hj Hne. exact (H j (Hsub j Hj) Hne). Qed.

Lemma bs_live_ext_mono : forall bs K K' i,
  (forall x, K' x -> K x) -> bs_live_ext bs K' i -> bs_live_ext bs K i.
Proof.
  intros bs K K' i Hsub [H | [Hk H]];
  [ left; exact H | right; split; [exact Hk | exact (Hsub i H)] ].
Qed.

Lemma live_ext_mono : forall es K K' i,
  (forall x, K' x -> K x) -> live_ext es K' i -> live_ext es K i.
Proof.
  intros es K K' i Hsub [H | [Hk H]];
  [ left; exact H | right; split; [exact Hk | exact (Hsub i H)] ].
Qed.

Lemma rel_b_weaken : forall phi K b b_o, rel_b phi K b b_o ->
  forall K', (forall i, K' i -> K i) -> rel_b phi K' b b_o
with rel_bs_weaken : forall phi K bs bs_o, rel_bs phi K bs bs_o ->
  forall K', (forall i, K' i -> K i) -> rel_bs phi K' bs bs_o.
Proof.
  { intros phi K b b_o H; destruct H; intros K' Hsub.
    - apply relb_plain; assumption.
    - apply relb_get.
    - apply relb_set. eapply slot_free_weaken; eassumption.
    - apply relb_tee. eapply slot_free_weaken; eassumption.
    - apply relb_block; [ assumption |]. eapply rel_bs_weaken; eassumption.
    - apply relb_loop; [ assumption |]. eapply rel_bs_weaken; [ eassumption |].
      intros i [Hl | Hk]; [ left; exact Hl | right; exact (Hsub i Hk) ].
    - apply relb_if; try assumption; eapply rel_bs_weaken; eassumption. }
  { intros phi K bs bs_o H; destruct H; intros K' Hsub.
    - apply relbs_nil.
    - apply relbs_cons.
      + eapply rel_b_weaken; [ eassumption |].
        intros i Hi. eapply bs_live_ext_mono; eassumption.
      + eapply rel_bs_weaken; eassumption. }
Qed.

Lemma rel_e_weaken : forall phi K e e_o, rel_e phi K e e_o ->
  forall K', (forall i, K' i -> K i) -> rel_e phi K' e e_o
with rel_es_weaken : forall phi K es es_o, rel_es phi K es es_o ->
  forall K', (forall i, K' i -> K i) -> rel_es phi K' es es_o.
Proof.
  { intros phi K e e_o H; destruct H; intros K' Hsub.
    - apply rel_basic. eapply rel_b_weaken; eassumption.
    - apply rel_trap.
    - apply rel_ref.
    - apply rel_ref_extern.
    - apply rel_invoke.
    - apply rel_return_invoke.
    - apply rel_label.
      + eapply label_ok_weaken; eassumption.
      + eapply rel_es_weaken; eassumption.
      + eapply rel_es_weaken; [ eassumption |].
        intros i [Hl | Hk]; [ left; exact Hl | right; exact (Hsub i Hk) ].
    - eapply rel_frame; eassumption. }
  { intros phi K es es_o H; destruct H; intros K' Hsub.
    - apply rel_nil.
    - apply rel_cons.
      + eapply rel_e_weaken; [ eassumption |].
        intros i Hi. eapply live_ext_mono; eassumption.
      + eapply rel_es_weaken; eassumption. }
Qed.

(* ── Append and split, exact inverses of each other ───────────────── *)

Lemma es_kills_b_app : forall i es1 es2,
  es_kills_b i (es1 ++ es2) = es_kills_b i es1 || es_kills_b i es2.
Proof.
  intros i es1. induction es1 as [|e es1' IH]; intros es2; simpl.
  - reflexivity.
  - rewrite IH. apply Bool.orb_assoc.
Qed.

Lemma es_live_b_app : forall i es1 es2,
  es_live_b i (es1 ++ es2) =
  es_live_b i es1 || (negb (es_kills_b i es1) && es_live_b i es2).
Proof.
  intros i es1. induction es1 as [|e es1' IH]; intros es2; simpl.
  - reflexivity.
  - rewrite IH.
    destruct (ai_live i e), (ai_kills i e), (es_kills_b i es1'),
             (es_live_b i es1'), (es_live_b i es2); reflexivity.
Qed.

Lemma live_ext_app : forall es1 es2 K i,
  live_ext (es1 ++ es2) K i <-> live_ext es1 (live_ext es2 K) i.
Proof.
  intros es1 es2 K i. unfold live_ext.
  rewrite es_live_b_app. rewrite es_kills_b_app. split.
  - intros [H | [Hk H]].
    + apply Bool.orb_true_iff in H. destruct H as [H | H].
      * left. exact H.
      * apply Bool.andb_true_iff in H. destruct H as [Hn H].
        right. split; [ apply Bool.negb_true_iff in Hn; exact Hn | left; exact H ].
    + apply Bool.orb_false_iff in Hk. destruct Hk as [H1 H2].
      right. split; [ exact H1 | right; split; [ exact H2 | exact H ] ].
  - intros [H | [Hk H]].
    + left. rewrite H. reflexivity.
    + destruct H as [H | [Hk2 H]].
      * left. rewrite Hk. rewrite H. simpl. apply Bool.orb_true_r.
      * right. rewrite Hk. rewrite Hk2. split; [ reflexivity | exact H ].
Qed.

Lemma rel_es_app : forall phi K es1 X1 es2 X2,
  rel_es phi (live_ext es2 K) es1 X1 ->
  rel_es phi K es2 X2 ->
  rel_es phi K (es1 ++ es2) (X1 ++ X2).
Proof.
  intros phi K es1. induction es1 as [|e es1' IH]; intros X1 es2 X2 H1 H2.
  - inversion H1; subst; simpl. exact H2.
  - inversion H1; subst. simpl. apply rel_cons.
    + eapply rel_e_weaken; [ eassumption |].
      intros i Hi. apply live_ext_app. exact Hi.
    + apply IH; assumption.
Qed.

Lemma rel_es_split : forall phi K es1 es2 X,
  rel_es phi K (es1 ++ es2) X ->
  exists X1 X2, X = X1 ++ X2 /\
    rel_es phi (live_ext es2 K) es1 X1 /\
    rel_es phi K es2 X2.
Proof.
  intros phi K es1. induction es1 as [|e es1' IH]; intros es2 X H; simpl in H.
  - exists nil, X. split; [reflexivity | split; [ apply rel_nil | exact H ]].
  - inversion H; subst.
    destruct (IH es2 es_o H6) as [X1 [X2 [Heq [Hr1 Hr2]]]]. subst es_o.
    exists (e_o :: X1), X2. split; [reflexivity | split; [| exact Hr2]].
    apply rel_cons; [| exact Hr1].
    eapply rel_e_weaken; [ eassumption |].
    intros i Hi. apply live_ext_app. exact Hi.
Qed.

(* ── Values: no local indices, so they relate to themselves ───────── *)

Lemma live_v_to_e : forall i v,
  ai_live i (v_to_e v) = false /\ ai_kills i (v_to_e v) = false.
Proof.
  intros i v. destruct v as [n | vv | vr]; simpl; try (split; reflexivity).
  destruct vr; simpl; split; reflexivity.
Qed.

Lemma live_v_to_e_list : forall i vs,
  es_live_b i (v_to_e_list vs) = false /\ es_kills_b i (v_to_e_list vs) = false.
Proof.
  intros i vs. induction vs as [|v vs' IH]; simpl; [ split; reflexivity |].
  destruct IH as [H1 H2]. destruct (live_v_to_e i v) as [Ha Hb].
  rewrite Ha. rewrite Hb. rewrite H1. rewrite H2. split; reflexivity.
Qed.

Lemma live_ext_v_to_e_list : forall vs K i, live_ext (v_to_e_list vs) K i <-> K i.
Proof.
  intros vs K i. unfold live_ext.
  destruct (live_v_to_e_list i vs) as [H1 H2]. rewrite H1. rewrite H2. split.
  - intros [Habs | [_ H]]; [ discriminate Habs | exact H ].
  - intros H. right. split; [reflexivity | exact H].
Qed.

Lemma rel_e_v_to_e : forall phi K v, rel_e phi K (v_to_e v) (v_to_e v).
Proof.
  intros phi K v. destruct v as [n | vv | vr]; simpl.
  - apply rel_basic. apply relb_plain. reflexivity.
  - apply rel_basic. apply relb_plain. reflexivity.
  - destruct vr as [t | a | e]; simpl.
    + apply rel_basic. apply relb_plain. reflexivity.
    + apply rel_ref.
    + apply rel_ref_extern.
Qed.

Lemma rel_es_v_to_e_list : forall phi K vs,
  rel_es phi K (v_to_e_list vs) (v_to_e_list vs).
Proof.
  intros phi K vs. induction vs as [|v vs' IH]; simpl.
  - apply rel_nil.
  - apply rel_cons; [ apply rel_e_v_to_e | exact IH ].
Qed.

(* ── An induction principle that reaches into nested instruction lists ──
   The generated basic_instruction_ind gives no hypothesis about the bodies
   of BI_block / BI_loop / BI_if, since those are *lists* of instructions.
   This is the standard strengthening, written as a Fixpoint because the
   list recursion has to be a local fix for the guard checker. *)
Fixpoint bi_ind' (P : basic_instruction -> Prop)
  (Hplain : forall b, plain_b b = true -> P b)
  (Hget : forall i, P (BI_local_get i))
  (Hset : forall i, P (BI_local_set i))
  (Htee : forall i, P (BI_local_tee i))
  (Hblock : forall bt bs, Forall P bs -> P (BI_block bt bs))
  (Hloop : forall bt bs, Forall P bs -> P (BI_loop bt bs))
  (Hif : forall bt b1 b2, Forall P b1 -> Forall P b2 -> P (BI_if bt b1 b2))
  (b : basic_instruction) {struct b} : P b :=
  let fix fa (bs : list basic_instruction) : Forall P bs :=
    match bs with
    | nil => Forall_nil P
    | x :: xs =>
        Forall_cons x (bi_ind' P Hplain Hget Hset Htee Hblock Hloop Hif x) (fa xs)
    end in
  match b as b0 return P b0 with
  | BI_local_get i => Hget i
  | BI_local_set i => Hset i
  | BI_local_tee i => Htee i
  | BI_block bt bs => Hblock bt bs (fa bs)
  | BI_loop bt bs => Hloop bt bs (fa bs)
  | BI_if bt b1 b2 => Hif bt b1 b2 (fa b1) (fa b2)
  | b0 => Hplain b0 eq_refl
  end.

(* ── The identity case ────────────────────────────────────────────────
   When the guard rejects a function the pass returns phi = empty, and the
   function comes back unchanged.  The relation has to cover that too --
   a rejected function is still called from somewhere -- so every program
   must relate to itself under empty.  This is why the obligations are
   stated per-write rather than as a blanket "no writes here" side
   condition: under empty, slot_free degrades to j <> i', which is free. *)

Lemma slot_free_empty : forall K i', slot_free empty K i'.
Proof.
  intros K i' j Hj Hne Habs.
  rewrite ! apply_phi_local_empty in Habs. exact (Hne Habs).
Qed.

Lemma rel_bs_refl_aux : forall bs,
  Forall (fun b => forall K, rel_b empty K b b) bs ->
  forall K, rel_bs empty K bs bs.
Proof.
  intros bs H. induction H as [| x xs Hx Hxs IH]; intros K.
  - apply relbs_nil.
  - apply relbs_cons; [ apply Hx | apply IH ].
Qed.

(* Reflexivity.  The only structural condition left is on loop bodies, per
   label_ok; nothing about phi is required, since under empty slot_free
   degrades to j <> i'.  So a function the interval guard rejects for any
   other reason -- a local written twice, or read before its def -- still
   relates to itself, which is what the top-level statement needs, because
   coalesce_module rewrites every function and leaves the rejected ones
   alone. *)
(* The pass's nesting guard, as a predicate: every structured body is
   branch-free or write-free.  The check is shallow on purpose -- either
   property holds of nested bodies a fortiori -- and it is exactly what
   relb_block, relb_loop and relb_if ask for. *)
(* bi_guarded and bs_guarded moved to coalesce_locals.v: func_supported
   checks them, so the pass and the proof share one definition. *)

Lemma bi_writes_guarded : forall b, bi_writes b = false -> bi_guarded b = true.
Proof.
  intros b Hw. destruct b; cbn [bi_guarded]; try reflexivity;
  unfold body_ok_b.
  - rewrite bi_writes_block in Hw. rewrite Hw. apply Bool.orb_true_r.
  - rewrite bi_writes_loop in Hw. rewrite Hw. apply Bool.orb_true_r.
  - rewrite bi_writes_if in Hw. apply Bool.orb_false_iff in Hw.
    destruct Hw as [H1 H2]. rewrite H1. rewrite H2.
    rewrite ! Bool.orb_true_r. reflexivity.
Qed.

Lemma bs_writes_guarded : forall bs, bs_writes bs = false -> bs_guarded bs = true.
Proof.
  intros bs. induction bs as [|b bs' IH]; intros Hw; simpl in *; [reflexivity |].
  apply Bool.orb_false_iff in Hw. destruct Hw as [H1 H2].
  rewrite (bi_writes_guarded b H1). simpl. exact (IH H2).
Qed.

(* Branch-freedom is hereditary too, so it guards just as well. *)
Lemma bi_nobr_guarded : forall b, bi_br b = false -> bi_guarded b = true.
Proof.
  intros b Hb. destruct b; cbn [bi_guarded]; try reflexivity;
  unfold body_ok_b.
  - rewrite bi_br_block in Hb. rewrite Hb. reflexivity.
  - rewrite bi_br_loop in Hb. rewrite Hb. reflexivity.
  - rewrite bi_br_if in Hb. apply Bool.orb_false_iff in Hb.
    destruct Hb as [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma bs_nobr_guarded : forall bs, bs_br bs = false -> bs_guarded bs = true.
Proof.
  intros bs. induction bs as [|b bs' IH]; intros Hb; simpl in *; [reflexivity |].
  apply Bool.orb_false_iff in Hb. destruct Hb as [H1 H2].
  rewrite (bi_nobr_guarded b H1). simpl. exact (IH H2).
Qed.

Lemma body_ok_b_guarded : forall bs, body_ok_b bs = true -> bs_guarded bs = true.
Proof.
  intros bs H. apply body_ok_b_ok in H. destruct H as [H | H];
  [ apply bs_nobr_guarded | apply bs_writes_guarded ]; exact H.
Qed.

Lemma rel_bs_refl_forall : forall bs,
  Forall (fun b => bi_guarded b = true -> forall K, rel_b empty K b b) bs ->
  bs_guarded bs = true ->
  forall K, rel_bs empty K bs bs.
Proof.
  intros bs H. induction H as [| x xs Hx Hxs IH]; intros Hlf K; simpl in Hlf.
  - apply relbs_nil.
  - apply Bool.andb_true_iff in Hlf. destruct Hlf as [Hx' Hxs'].
    apply relbs_cons; [ apply Hx; exact Hx' | apply IH; exact Hxs' ].
Qed.

Lemma rel_b_refl : forall b, bi_guarded b = true -> forall K, rel_b empty K b b.
Proof.
  intros b. induction b using bi_ind'; intros Hlf K.
  - apply relb_plain. assumption.
  - rewrite <- (apply_phi_local_empty i) at 2. apply relb_get.
  - rewrite <- (apply_phi_local_empty i) at 2. apply relb_set. apply slot_free_empty.
  - rewrite <- (apply_phi_local_empty i) at 2. apply relb_tee. apply slot_free_empty.
  - cbn [bi_guarded] in Hlf.
    apply relb_block; [ apply body_ok_b_ok; exact Hlf |].
    apply rel_bs_refl_forall; [ exact H | apply body_ok_b_guarded; exact Hlf ].
  - cbn [bi_guarded] in Hlf.
    apply relb_loop; [ apply body_ok_b_ok; exact Hlf |].
    apply rel_bs_refl_forall; [ exact H | apply body_ok_b_guarded; exact Hlf ].
  - cbn [bi_guarded] in Hlf. apply Bool.andb_true_iff in Hlf.
    destruct Hlf as [Hl1 Hl2].
    apply relb_if;
      [ apply body_ok_b_ok; exact Hl1 | apply body_ok_b_ok; exact Hl2 | |];
    apply rel_bs_refl_forall;
      [ exact H | apply body_ok_b_guarded; exact Hl1
      | exact H0 | apply body_ok_b_guarded; exact Hl2 ].
Qed.

Lemma rel_bs_refl : forall bs, bs_guarded bs = true -> forall K, rel_bs empty K bs bs.
Proof.
  intros bs Hlf. apply rel_bs_refl_forall; [| exact Hlf ].
  apply Forall_forall. intros x _. apply rel_b_refl.
Qed.

Lemma rel_b_plain_inv : forall phi K b b_o,
  rel_b phi K b b_o -> plain_b b = true -> b_o = b.
Proof.
  intros phi K b b_o H Hp. destruct H; try reflexivity;
  simpl in Hp; discriminate Hp.
Qed.

Lemma rel_e_v_inv : forall phi K v e_o, rel_e phi K (v_to_e v) e_o -> e_o = v_to_e v.
Proof.
  intros phi K v e_o H.
  destruct v as [n | vv | vr]; simpl in H;
  [ | | destruct vr as [t | a | e]; simpl in H ];
  inversion H; subst; try reflexivity;
  match goal with
  | Hb : rel_b _ _ ?b ?bo |- _ =>
      assert (bo = b) as Hbe by (eapply rel_b_plain_inv; [ exact Hb | reflexivity ]);
      rewrite Hbe; reflexivity
  end.
Qed.

Lemma rel_es_v_to_e_list_inv : forall phi K vs X,
  rel_es phi K (v_to_e_list vs) X -> X = v_to_e_list vs.
Proof.
  intros phi K vs. induction vs as [|v vs' IH]; intros X H; simpl in H.
  - inversion H; subst. reflexivity.
  - inversion H; subst. simpl. f_equal.
    + eapply rel_e_v_inv; eassumption.
    + apply IH. assumption.
Qed.

Lemma live_ext_nil : forall K i, live_ext nil K i <-> K i.
Proof.
  intros K i. unfold live_ext. simpl. split.
  - intros [Habs | [_ H]]; [ discriminate Habs | exact H ].
  - intros H. right. split; [ reflexivity | exact H ].
Qed.

(* ── Basic-instruction lists lifted to administrative ones ────────── *)

Lemma es_live_to_e_list : forall i bs, es_live_b i (to_e_list bs) = bs_live_b i bs.
Proof.
  intros i bs. induction bs as [|b bs' IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma es_kills_to_e_list : forall i bs, es_kills_b i (to_e_list bs) = bs_kills_b i bs.
Proof.
  intros i bs. induction bs as [|b bs' IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma live_ext_to_e_list : forall bs K i,
  live_ext (to_e_list bs) K i <-> bs_live_ext bs K i.
Proof.
  intros bs K i. unfold live_ext, bs_live_ext.
  rewrite es_live_to_e_list. rewrite es_kills_to_e_list. split; intro H; exact H.
Qed.

Lemma rel_es_to_e_list : forall phi K bs bs_o,
  rel_bs phi K bs bs_o -> rel_es phi K (to_e_list bs) (to_e_list bs_o).
Proof.
  intros phi K bs bs_o H. induction H as [| phi K b b_o bs bs_o Hb Hbs IH]; simpl.
  - apply rel_nil.
  - apply rel_cons; [| exact IH ].
    apply rel_basic. eapply rel_b_weaken; [ eassumption |].
    intros i Hi. apply live_ext_to_e_list. exact Hi.
Qed.

(* ── Plain instructions ────────────────────────────────────────────
   Most reduce rules consume a list of values plus one instruction that
   mentions no local, and produce values or a trap.  On such lists the
   rename is the identity and the live set is empty, so both sides of the
   simulation are the same list and the frame agreement is untouched.
   This is what makes the bulk of the ~70 cases uniform. *)

Definition ai_plain (e : administrative_instruction) : bool :=
  match e with
  | AI_basic b => plain_b b
  | AI_label _ _ _ => false
  | AI_frame _ _ _ => false
  | _ => true
  end.

Definition es_plain (es : list administrative_instruction) : bool :=
  forallb ai_plain es.

Lemma es_plain_cons : forall e es,
  es_plain (e :: es) = ai_plain e && es_plain es.
Proof. reflexivity. Qed.

Lemma es_plain_app : forall es1 es2,
  es_plain es1 = true -> es_plain es2 = true -> es_plain (es1 ++ es2) = true.
Proof.
  intros es1. induction es1 as [|e es1' IH]; intros es2 H1 H2; simpl in *;
  [exact H2 |].
  apply Bool.andb_true_iff in H1. destruct H1 as [Ha Hb].
  rewrite Ha. simpl. apply IH; assumption.
Qed.

Lemma es_plain_cat : forall es1 es2,
  es_plain es1 = true -> es_plain es2 = true -> es_plain (seq.cat es1 es2) = true.
Proof. exact es_plain_app. Qed.

Lemma ai_plain_v_to_e : forall v, ai_plain (v_to_e v) = true.
Proof.
  intros v. destruct v as [ | | vr]; simpl; try reflexivity. destruct vr; reflexivity.
Qed.

Lemma es_plain_v_to_e_list : forall vs, es_plain (v_to_e_list vs) = true.
Proof.
  intros vs. induction vs as [|v vs' IH]; simpl; [reflexivity |].
  rewrite ai_plain_v_to_e. simpl. exact IH.
Qed.

Lemma es_plain_const_list : forall es,
  is_true (const_list es) -> es_plain es = true.
Proof.
  intros es. induction es as [|e es' IH]; intros Hc; simpl; [reflexivity |].
  simpl in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
  rewrite (IH H2). rewrite Bool.andb_true_r.
  destruct e; simpl in *; try reflexivity; try discriminate H1.
  destruct b; simpl in *; try reflexivity; try discriminate H1.
Qed.

Lemma es_plain_result_to_stack : forall r, es_plain (result_to_stack r) = true.
Proof.
  intros r. destruct r; simpl; [ apply es_plain_v_to_e_list | reflexivity ].
Qed.

(* "Neutral" is stronger than "plain": it also excludes AI_trap, which the
   rename leaves alone but which kills every local.  Only the neutral ones
   leave the live set where it was. *)
Definition ai_neutral (e : administrative_instruction) : bool :=
  match e with
  | AI_basic b => plain_b b
  | AI_trap => false
  | AI_label _ _ _ => false
  | AI_frame _ _ _ => false
  | _ => true
  end.

Definition es_neutral (es : list administrative_instruction) : bool :=
  forallb ai_neutral es.

Lemma ai_neutral_plain : forall e, ai_neutral e = true -> ai_plain e = true.
Proof. intros e H. destruct e; simpl in *; first [ reflexivity | assumption ]. Qed.

Lemma es_neutral_plain : forall es, es_neutral es = true -> es_plain es = true.
Proof.
  intros es. induction es as [|e es' IH]; intros H; simpl in *; [reflexivity |].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  rewrite (ai_neutral_plain e H1). simpl. exact (IH H2).
Qed.

Lemma ai_neutral_live : forall i e,
  ai_neutral e = true -> ai_live i e = false /\ ai_kills i e = false.
Proof.
  intros i e H. destruct e; simpl in *; try (split; reflexivity);
  try discriminate H.
  destruct b; simpl in *; try (split; reflexivity); discriminate H.
Qed.

Lemma es_neutral_live : forall i es,
  es_neutral es = true -> es_live_b i es = false /\ es_kills_b i es = false.
Proof.
  intros i es. induction es as [|e es' IH]; intros H; simpl in *;
  [split; reflexivity |].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  destruct (ai_neutral_live i e H1) as [Ha Hb]. destruct (IH H2) as [Hc Hd].
  rewrite Ha. rewrite Hb. rewrite Hc. rewrite Hd. split; reflexivity.
Qed.

Lemma live_ext_neutral : forall es K i,
  es_neutral es = true -> (live_ext es K i <-> K i).
Proof.
  intros es K i H. destruct (es_neutral_live i es H) as [H1 H2].
  unfold live_ext. rewrite H1. rewrite H2. split.
  - intros [Habs | [_ HK]]; [ discriminate Habs | exact HK ].
  - intros HK. right. split; [reflexivity | exact HK].
Qed.

(* Nothing is live after a trap. *)
Lemma live_ext_trap : forall K i, live_ext [AI_trap] K i -> False.
Proof.
  intros K i [Habs | [Hk _]]; simpl in *; discriminate.
Qed.

Lemma es_neutral_app : forall es1 es2,
  es_neutral es1 = true -> es_neutral es2 = true -> es_neutral (es1 ++ es2) = true.
Proof.
  intros es1. induction es1 as [|e es1' IH]; intros es2 H1 H2; simpl in *;
  [exact H2 |].
  apply Bool.andb_true_iff in H1. destruct H1 as [Ha Hb].
  rewrite Ha. simpl. apply IH; assumption.
Qed.

Lemma es_neutral_cat : forall es1 es2,
  es_neutral es1 = true -> es_neutral es2 = true ->
  es_neutral (seq.cat es1 es2) = true.
Proof. exact es_neutral_app. Qed.

Lemma ai_neutral_v_to_e : forall v, ai_neutral (v_to_e v) = true.
Proof.
  intros v. destruct v as [ | | vr]; simpl; try reflexivity. destruct vr; reflexivity.
Qed.

Lemma es_neutral_v_to_e_list : forall vs, es_neutral (v_to_e_list vs) = true.
Proof.
  intros vs. induction vs as [|v vs' IH]; simpl; [reflexivity |].
  rewrite ai_neutral_v_to_e. simpl. exact IH.
Qed.

Lemma es_neutral_const_list : forall es,
  is_true (const_list es) -> es_neutral es = true.
Proof.
  intros es. induction es as [|e es' IH]; intros Hc; simpl; [reflexivity |].
  simpl in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
  rewrite (IH H2). rewrite Bool.andb_true_r.
  destruct e; simpl in *; try reflexivity; try discriminate H1.
  destruct b; simpl in *; try reflexivity; try discriminate H1.
Qed.

Lemma es_neutral_cons : forall e es,
  ai_neutral e = true -> es_neutral es = true -> es_neutral (e :: es) = true.
Proof. intros e es H1 H2. simpl. rewrite H1. exact H2. Qed.

(* result_to_stack is values or a trap, so it never keeps anything live. *)
Lemma live_ext_result_to_stack : forall r K i,
  live_ext (result_to_stack r) K i -> K i.
Proof.
  intros r K i H. destruct r; simpl in *.
  - apply (live_ext_neutral _ K i) in H; [ exact H | apply es_neutral_v_to_e_list ].
  - destruct (live_ext_trap K i H).
Qed.

Ltac neutral_atom := solve [ apply ai_neutral_v_to_e | reflexivity ].

Ltac neutral_solve :=
  solve [ reflexivity
        | apply es_neutral_v_to_e_list
        | apply es_neutral_const_list; assumption
        | apply es_neutral_app; neutral_solve
        | apply es_neutral_cat; neutral_solve
        | apply es_neutral_cons; [ neutral_atom | neutral_solve ] ].

(* Directional forms.  `apply` on the iff works on a goal but not in a
   hypothesis, so the tactic below aims at these instead. *)
Lemma live_ext_neutral_fwd : forall es K i,
  es_neutral es = true -> live_ext es K i -> K i.
Proof. intros es K i H. apply (live_ext_neutral es K i H). Qed.

Lemma live_ext_neutral_bwd : forall es K i,
  es_neutral es = true -> K i -> live_ext es K i.
Proof. intros es K i H. apply (live_ext_neutral es K i H). Qed.

(* ── Liveness of the shapes the structural rules produce ─────────── *)

Lemma es_live_singleton : forall i e, es_live_b i [e] = ai_live i e.
Proof.
  intros i e. simpl. destruct (ai_live i e), (ai_kills i e); reflexivity.
Qed.

Lemma es_kills_singleton : forall i e, es_kills_b i [e] = ai_kills i e.
Proof. intros i e. simpl. apply Bool.orb_false_r. Qed.

(* Values in front of a redex contribute nothing, so they can be peeled
   off both sides of a live-set comparison. *)
Lemma live_ext_const_app : forall vs es K i,
  is_true (const_list vs) -> (live_ext (vs ++ es) K i <-> live_ext es K i).
Proof.
  intros vs es K i Hc. split; intros H.
  - apply live_ext_app in H.
    refine (live_ext_neutral_fwd _ _ i _ H). apply es_neutral_const_list. exact Hc.
  - apply live_ext_app.
    apply live_ext_neutral_bwd; [ apply es_neutral_const_list; exact Hc | exact H ].
Qed.

(* Cons form of the above, for the many redexes written as an explicit
   stack of values in front of the instruction. *)
Lemma live_ext_neutral_cons : forall e es K i,
  ai_neutral e = true -> (live_ext (e :: es) K i <-> live_ext es K i).
Proof.
  intros e es K i H. destruct (ai_neutral_live i e H) as [Hl Hk].
  unfold live_ext. simpl. rewrite Hl. rewrite Hk. simpl.
  split; intros HH; exact HH.
Qed.

(* A label with an empty branch continuation is transparent: nothing can
   jump to it, so its live set is exactly its body's. *)
Lemma live_ext_label_nil : forall n b K i,
  live_ext [AI_label n nil b] K i <-> live_ext b K i.
Proof.
  intros n b K i. unfold live_ext.
  rewrite es_live_singleton. rewrite es_kills_singleton.
  rewrite ai_live_label. rewrite ai_kills_label. simpl.
  rewrite Bool.andb_false_r. rewrite Bool.orb_false_r.
  split; intros H; exact H.
Qed.

(* A label's live set is its body's, over a continuation extended with the
   branch target's reads.  This is an equality, not a containment: it is
   what makes the live set of a filled context equal the live set of its
   hole (live_ext_lfill below), which is what r_label needs in order to
   hand the invariant down and get it back. *)
Lemma live_ext_label : forall n a b K i,
  live_ext [AI_label n a b] K i <->
  live_ext b (fun j => es_live_b j a = true \/ K j) i.
Proof.
  intros n a b K i. unfold live_ext.
  rewrite es_live_singleton. rewrite es_kills_singleton.
  rewrite ai_live_label. rewrite ai_kills_label.
  destruct (es_live_b i b) eqn:Hb; destruct (es_kills_b i b) eqn:Hk;
  destruct (es_live_b i a) eqn:Ha; simpl; split;
  (intros [H | [H1 H2]];
   solve [ left; reflexivity
         | discriminate H
         | discriminate H1
         | right; split; [reflexivity |]; tauto
         | tauto ]).
Qed.

(* An activation is opaque: nothing outside it reads or writes its locals. *)
Lemma live_ext_frame : forall n fr es K i,
  live_ext [AI_frame n fr es] K i <-> K i.
Proof.
  intros n fr es K i. unfold live_ext.
  rewrite es_live_singleton. rewrite es_kills_singleton. simpl. split.
  - intros [Habs | [_ H]]; [ discriminate Habs | exact H ].
  - intros H. right. split; [ reflexivity | exact H ].
Qed.

(* Blocks, loops and ifs never kill: bi_kills only looks at local.set and
   local.tee.  Their liveness is their body's. *)
Lemma live_ext_block : forall bt bs K i,
  live_ext [AI_basic (BI_block bt bs)] K i <-> (bs_live_b i bs = true \/ K i).
Proof.
  intros bt bs K i. unfold live_ext.
  rewrite es_live_singleton. rewrite es_kills_singleton.
  cbn [ai_live ai_kills bi_kills]. rewrite bi_live_block.
  split.
  - intros [H | [_ H]]; [ left; exact H | right; exact H ].
  - intros [H | H]; [ left; exact H | right; split; [reflexivity | exact H] ].
Qed.

Lemma live_ext_if : forall bt bs1 bs2 K i,
  live_ext [AI_basic (BI_if bt bs1 bs2)] K i <->
  ((bs_live_b i bs1 || bs_live_b i bs2) = true \/ K i).
Proof.
  intros bt bs1 bs2 K i. unfold live_ext.
  rewrite es_live_singleton. rewrite es_kills_singleton.
  cbn [ai_live ai_kills bi_kills]. rewrite bi_live_if.
  split.
  - intros [H | [_ H]]; [ left; exact H | right; exact H ].
  - intros [H | H]; [ left; exact H | right; split; [reflexivity | exact H] ].
Qed.

Lemma live_ext_loop : forall bt bs K i,
  live_ext [AI_basic (BI_loop bt bs)] K i <-> (bs_live_b i bs = true \/ K i).
Proof.
  intros bt bs K i. unfold live_ext.
  rewrite es_live_singleton. rewrite es_kills_singleton.
  cbn [ai_live ai_kills bi_kills]. rewrite bi_live_loop.
  split.
  - intros [H | [_ H]]; [ left; exact H | right; exact H ].
  - intros [H | H]; [ left; exact H | right; split; [reflexivity | exact H] ].
Qed.

(* Goal: the live set after the step is contained in the one before.  Either
   both lists are neutral (so both sets are K), or the step produced a trap
   or a result, after which nothing is live. *)
Ltac live_sub_solve :=
  let i := fresh "i" in let Hl := fresh "Hl" in
  intros i Hl;
  first [ destruct (live_ext_trap _ i Hl)
        | apply live_ext_neutral_bwd; [ solve [neutral_solve] |];
          solve [ exact (live_ext_result_to_stack _ _ i Hl)
                | refine (live_ext_neutral_fwd _ _ i _ Hl); solve [neutral_solve] ] ].

Lemma rel_e_plain : forall phi K e, ai_plain e = true -> rel_e phi K e e.
Proof.
  intros phi K e H. destruct e; simpl in H.
  - apply rel_basic. apply relb_plain. exact H.
  - apply rel_trap.
  - apply rel_ref.
  - apply rel_ref_extern.
  - apply rel_invoke.
  - apply rel_return_invoke.
  - discriminate H.
  - discriminate H.
Qed.

Lemma rel_es_plain : forall phi K es, es_plain es = true -> rel_es phi K es es.
Proof.
  intros phi K es. induction es as [|e es' IH]; intros H; simpl in H.
  - apply rel_nil.
  - apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    apply rel_cons; [ apply rel_e_plain; exact H1 | exact (IH H2) ].
Qed.

Lemma rel_e_plain_inv : forall phi K e e_o,
  rel_e phi K e e_o -> ai_plain e = true -> e_o = e.
Proof.
  intros phi K e e_o H Hp. destruct H; simpl in Hp; try reflexivity;
  try discriminate Hp.
  f_equal. eapply rel_b_plain_inv; eassumption.
Qed.

Lemma rel_es_plain_inv : forall phi K es es_o,
  rel_es phi K es es_o -> es_plain es = true -> es_o = es.
Proof.
  intros phi K es es_o H. induction H as [| phi K e e_o es es_o He Hes IH];
  intros Hp; simpl in Hp; [reflexivity |].
  apply Bool.andb_true_iff in Hp. destruct Hp as [H1 H2].
  rewrite (IH H2). f_equal. eapply rel_e_plain_inv; eassumption.
Qed.

(* ── Inversion ────────────────────────────────────────────────────
   The relation is the graph of the rename, so knowing the source shape
   pins down the target.  These package the inversions the simulation
   needs case by case. *)

Lemma rel_es_nil_inv : forall phi K es_o, rel_es phi K nil es_o -> es_o = nil.
Proof. intros phi K es_o H. inversion H; reflexivity. Qed.

Lemma rel_es_cons_inv : forall phi K e es es_o,
  rel_es phi K (e :: es) es_o ->
  exists e_o es_o', es_o = e_o :: es_o' /\
    rel_e phi (live_ext es K) e e_o /\ rel_es phi K es es_o'.
Proof.
  intros phi K e es es_o H. inversion H; subst.
  eexists; eexists; split; [reflexivity | split; eassumption].
Qed.

Lemma rel_e_basic_inv : forall phi K b e_o,
  rel_e phi K (AI_basic b) e_o -> exists b_o, e_o = AI_basic b_o /\ rel_b phi K b b_o.
Proof.
  intros phi K b e_o H. inversion H; subst.
  eexists; split; [reflexivity | eassumption].
Qed.

Lemma rel_b_get_inv : forall phi K j b_o,
  rel_b phi K (BI_local_get j) b_o -> b_o = BI_local_get (apply_phi_local phi j).
Proof.
  intros phi K j b_o H. inversion H; subst; [| reflexivity].
  simpl in H0. discriminate H0.
Qed.

Lemma rel_b_set_inv : forall phi K j b_o,
  rel_b phi K (BI_local_set j) b_o ->
  b_o = BI_local_set (apply_phi_local phi j) /\ slot_free phi K j.
Proof.
  intros phi K j b_o H. inversion H; subst.
  - simpl in H0. discriminate H0.
  - split; [reflexivity | assumption].
Qed.

Lemma rel_b_tee_inv : forall phi K j b_o,
  rel_b phi K (BI_local_tee j) b_o ->
  b_o = BI_local_tee (apply_phi_local phi j) /\ slot_free phi K j.
Proof.
  intros phi K j b_o H. inversion H; subst.
  - simpl in H0. discriminate H0.
  - split; [reflexivity | assumption].
Qed.

Lemma rel_b_block_inv : forall phi K bt bs b_o,
  rel_b phi K (BI_block bt bs) b_o ->
  exists bs_o, b_o = BI_block bt bs_o /\ body_ok bs /\
    rel_bs phi K bs bs_o.
Proof.
  intros phi K bt bs b_o H. inversion H; subst.
  - simpl in H0. discriminate H0.
  - eexists; split; [reflexivity | split; assumption].
Qed.

Lemma rel_b_loop_inv : forall phi K bt bs b_o,
  rel_b phi K (BI_loop bt bs) b_o ->
  exists bs_o, b_o = BI_loop bt bs_o /\ body_ok bs /\
    rel_bs phi (fun i => bs_live_b i bs = true \/ K i) bs bs_o.
Proof.
  intros phi K bt bs b_o H. inversion H; subst.
  - simpl in H0. discriminate H0.
  - eexists; split; [reflexivity | split; assumption].
Qed.

Lemma rel_b_if_inv : forall phi K bt bs1 bs2 b_o,
  rel_b phi K (BI_if bt bs1 bs2) b_o ->
  exists b1_o b2_o, b_o = BI_if bt b1_o b2_o /\
    body_ok bs1 /\ body_ok bs2 /\
    rel_bs phi K bs1 b1_o /\ rel_bs phi K bs2 b2_o.
Proof.
  intros phi K bt bs1 bs2 b_o H. inversion H; subst.
  - simpl in H0. discriminate H0.
  - eexists; eexists; split;
    [reflexivity | split; [| split; [| split]]; assumption].
Qed.

(* The relation preserves length, so an empty target forces an empty
   source.  rs_trap needs this to know the optimized redex is not already
   a bare trap. *)
Lemma rel_es_nil_inv_r : forall phi K es, rel_es phi K es nil -> es = nil.
Proof. intros phi K es H. inversion H; reflexivity. Qed.

Lemma rel_e_label_inv : forall phi K n a b e_o,
  rel_e phi K (AI_label n a b) e_o ->
  exists a_o b_o, e_o = AI_label n a_o b_o /\ label_ok a b K /\
    rel_es phi K a a_o /\
    rel_es phi (fun i => es_live_b i a = true \/ K i) b b_o.
Proof.
  intros phi K n a b e_o H. inversion H; subst.
  eexists; eexists; split; [reflexivity | split; [assumption | split; assumption]].
Qed.

Lemma rel_e_frame_inv : forall phi K n fr es e_o,
  rel_e phi K (AI_frame n fr es) e_o ->
  exists fr_o es_o psi, e_o = AI_frame n fr_o es_o /\
    frames_agree psi (es_live es) fr fr_o /\
    rel_es psi (fun _ => False) es es_o.
Proof.
  intros phi K n fr es e_o H. inversion H; subst.
  eexists; eexists; eexists; split; [reflexivity | split; eassumption].
Qed.

Lemma es_plain_cons_plain : forall e es,
  ai_plain e = true -> es_plain es = true -> es_plain (e :: es) = true.
Proof. intros e es H1 H2. simpl. rewrite H1. exact H2. Qed.

(* Recursive rather than "split all appends, then close": an append lemma
   can also fire on a singleton list, and then only the first of the two
   goals would get a closer.  The cons case is needed because a stack
   operand $V v with v abstract does not compute. *)
Ltac plain_atom := solve [ apply ai_plain_v_to_e | reflexivity ].

Ltac plain_solve :=
  solve [ reflexivity
        | apply es_plain_v_to_e_list
        | apply es_plain_result_to_stack
        | apply es_plain_const_list; assumption
        | apply es_plain_app; plain_solve
        | apply es_plain_cat; plain_solve
        | apply es_plain_cons_plain; [ plain_atom | plain_solve ] ].

(* ══════════════════════════════════════════════════════════════════
   Label contexts.
   ══════════════════════════════════════════════════════════════════

   r_label proves a step of [lfill lh es] from a step of the fragment es.
   To use it we must decompose the relation at [lfill lh es], step the
   hole, and reassemble -- so we need the context's own relation plus the
   read-set the context contributes to the hole. *)

Fixpoint lh_K {k} (lh : lholed k) (K : N -> Prop) : N -> Prop :=
  match lh with
  | LH_base _ es' => live_ext es' K
  | LH_rec _ _ _ es' lh' es'' =>
      lh_K lh' (fun i => es_live_b i es' = true \/ live_ext es'' K i)
  end.

(* Filling a context does not merely *contain* the hole's live set -- it is
   equal to it, once the continuations are folded into lh_K.  Equality is
   what r_label needs: it passes the frame agreement down to the hole, and
   the successor's agreement back up, at exactly the sets the recursive
   call produces.  No label_ok condition enters here; that one constrains
   the *relation*, not the liveness. *)
Lemma live_ext_lfill : forall k (lh : lholed k) X K i,
  live_ext (lfill lh X) K i <-> live_ext X (lh_K lh K) i.
Proof.
  intros k lh. induction lh as [vs es' | k vs n es' lh IH es''];
  intros X K i; simpl.
  - rewrite live_ext_const_app; [| apply v_to_e_const ].
    apply live_ext_app.
  - rewrite live_ext_const_app; [| apply v_to_e_const ].
    change (live_ext (AI_label n es' (lfill lh X) :: es'') K i <->
            live_ext X (lh_K lh (fun j => es_live_b j es' = true \/
                                          live_ext es'' K j)) i).
    change (AI_label n es' (lfill lh X) :: es'')
      with ([AI_label n es' (lfill lh X)] ++ es'').
    rewrite live_ext_app. rewrite live_ext_label. apply IH.
Qed.

(* The writes a context contributes, independently of its hole. *)
Fixpoint lh_writes {k} (lh : lholed k) : bool :=
  match lh with
  | LH_base _ es' => es_writes es'
  | LH_rec _ _ _ es' lh' es'' => es_writes es' || lh_writes lh' || es_writes es''
  end.

Lemma es_writes_v_to_e_list : forall vs, es_writes (v_to_e_list vs) = false.
Proof.
  intros vs. induction vs as [|v vs' IH]; simpl; [reflexivity |].
  rewrite IH. destruct v as [ | | vr]; simpl; try reflexivity.
  destruct vr; reflexivity.
Qed.

(* Filling adds exactly the hole's writes to the context's own.  Both
   directions of the nesting condition follow from this one equation. *)
Lemma es_writes_lfill : forall k (lh : lholed k) X,
  es_writes (lfill lh X) = lh_writes lh || es_writes X.
Proof.
  intros k lh. induction lh as [vs es' | k vs n es' lh IH es'']; intros X; simpl.
  - rewrite ! es_writes_app. rewrite es_writes_v_to_e_list.
    destruct (es_writes X), (es_writes es'); reflexivity.
  - rewrite ! es_writes_app. rewrite es_writes_v_to_e_list.
    cbn [es_writes]. rewrite ai_writes_label. rewrite IH.
    destruct (es_writes es'), (lh_writes lh), (es_writes X), (es_writes es'');
    reflexivity.
Qed.

Lemma lfill_nowrite : forall k (lh : lholed k) X,
  lh_writes lh = false -> es_writes X = false -> es_writes (lfill lh X) = false.
Proof.
  intros k lh X H1 H2. rewrite es_writes_lfill. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma lfill_nowrite_inv : forall k (lh : lholed k) X,
  es_writes (lfill lh X) = false -> lh_writes lh = false /\ es_writes X = false.
Proof.
  intros k lh X H. rewrite es_writes_lfill in H.
  apply Bool.orb_false_iff in H. exact H.
Qed.

(* The same for branches. *)
Fixpoint lh_br {k} (lh : lholed k) : bool :=
  match lh with
  | LH_base _ es' => es_br es'
  | LH_rec _ _ _ es' lh' es'' => es_br es' || lh_br lh' || es_br es''
  end.

Lemma es_br_v_to_e_list : forall vs, es_br (v_to_e_list vs) = false.
Proof.
  intros vs. induction vs as [|v vs' IH]; simpl; [reflexivity |].
  rewrite IH. destruct v as [ | | vr]; simpl; try reflexivity.
  destruct vr; reflexivity.
Qed.

Lemma es_br_lfill : forall k (lh : lholed k) X,
  es_br (lfill lh X) = lh_br lh || es_br X.
Proof.
  intros k lh. induction lh as [vs es' | k vs n es' lh IH es'']; intros X; simpl.
  - rewrite ! es_br_app. rewrite es_br_v_to_e_list.
    destruct (es_br X), (es_br es'); reflexivity.
  - rewrite ! es_br_app. rewrite es_br_v_to_e_list.
    cbn [es_br]. rewrite ai_br_label. rewrite IH.
    destruct (es_br es'), (lh_br lh), (es_br X), (es_br es''); reflexivity.
Qed.

(* A branch-free list has no branch pending in it -- the direct analogue of
   trapping_no_br, and the reason the branch-free disjunct of label_ok
   discharges rs_br. *)
Lemma es_br_no_br : forall k (lh : lholed k) vs j,
  es_br (lfill lh (vs ++ [AI_basic (BI_br j)])) = false -> False.
Proof.
  intros k lh vs j H. rewrite es_br_lfill in H. rewrite es_br_app in H.
  apply Bool.orb_false_iff in H. destruct H as [_ H].
  apply Bool.orb_false_iff in H. destruct H as [_ H].
  cbn in H. discriminate H.
Qed.

(* The same for hazards, which is what label_ok is stated with. *)
Fixpoint lh_hazard {k} (lh : lholed k) : bool :=
  match lh with
  | LH_base _ es' => es_hazard es'
  | LH_rec _ _ _ es' lh' es'' => es_hazard es' || lh_hazard lh' || es_hazard es''
  end.

Lemma es_hazard_v_to_e_list : forall vs, es_hazard (v_to_e_list vs) = false.
Proof.
  intros vs. apply es_hazard_const. apply v_to_e_const.
Qed.

Lemma es_hazard_lfill : forall k (lh : lholed k) X,
  es_hazard (lfill lh X) = lh_hazard lh || es_hazard X.
Proof.
  intros k lh. induction lh as [vs es' | k vs n es' lh IH es'']; intros X; simpl.
  - rewrite ! es_hazard_app. rewrite es_hazard_v_to_e_list.
    destruct (es_hazard X), (es_hazard es'); reflexivity.
  - rewrite ! es_hazard_app. rewrite es_hazard_v_to_e_list.
    cbn [es_hazard]. rewrite ai_hazard_label. rewrite IH.
    destruct (es_hazard es'), (lh_hazard lh), (es_hazard X), (es_hazard es'');
    reflexivity.
Qed.

Lemma es_kills_v_to_e_list : forall i vs, es_kills_b i (v_to_e_list vs) = false.
Proof.
  intros i vs. destruct (live_v_to_e_list i vs) as [_ H]. exact H.
Qed.

(* The label_ok obligations a context imposes, once its hole is filled.
   Stated over the context so that r_label can take it apart and, after
   stepping the hole, put it back.  The per-level live-out follows lh_K's
   recursion, since that is the K each label actually sees. *)
Fixpoint lh_labels_ok {k} (lh : lholed k) (es : list administrative_instruction)
                      (K : N -> Prop) : Prop :=
  match lh with
  | LH_base _ _ => True
  | LH_rec _ _ _ es' lh' es'' =>
      label_ok es' (lfill lh' es) (live_ext es'' K) /\
      lh_labels_ok lh' es (fun i => es_live_b i es' = true \/ live_ext es'' K i)
  end.

(* Filling any context around a list that has trapped still gives a list
   that has trapped: the two contexts compose.  The base case is exactly
   the library's push_front_vs / push_back_es pair. *)
Lemma trapping_lfill : forall k (lh : lholed k) es,
  trapping es -> trapping (lfill lh es).
Proof.
  intros k lh. induction lh as [vs0 es0 | k vs0 n es0 lh IH es0'];
  intros es Htr.
  - destruct Htr as [k2 [lh2 Heq]]. subst es. simpl.
    exists k2, (lh_push_front_vs vs0 (lh_push_back_es es0 lh2)).
    rewrite (lfill_push_front_vs vs0 (lfill_push_back_es lh2 [AI_trap] es0)).
    reflexivity.
  - destruct (IH es Htr) as [k3 [lh3 Heq3]].
    exists (S k3), (LH_rec vs0 n es0 lh3 es0').
    simpl. rewrite Heq3. reflexivity.
Qed.

(* Reassociation used to expose the first non-constant instruction of a
   filled context, which is what const_list_concat_inv needs.  Stated with
   seq.cat on the outside because that is the shape lfill leaves behind. *)
Lemma cat_split_at_e : forall (a b : list administrative_instruction) e c,
  seq.cat a (seq.cat (b ++ [e]) c) = seq.cat (seq.cat a b) (e :: c).
Proof.
  intros a b e c. induction a as [| x a IH]; simpl.
  - induction b as [| y b IHb]; simpl;
    [ reflexivity | rewrite IHb; reflexivity ].
  - rewrite IH; reflexivity.
Qed.

Lemma not_const_br : forall j, ~ is_true (is_const (AI_basic (BI_br j))).
Proof. intros j H. discriminate H. Qed.

Lemma not_const_trap : ~ is_true (is_const AI_trap).
Proof. intros H. discriminate H. Qed.

Lemma not_const_label : forall n a b, ~ is_true (is_const (AI_label n a b)).
Proof. intros n a b H. discriminate H. Qed.

(* A list that has trapped has no branch pending in it.  Both sides of the
   equation are a constant prefix followed by a first non-constant
   instruction; comparing those, a br would have to be a trap or a label.
   Under matching labels the argument recurses. *)
Lemma trapping_no_br : forall k (lh : lholed k) vs j,
  is_true (const_list vs) ->
  trapping (lfill lh (vs ++ [AI_basic (BI_br j)])) -> False.
Proof.
  intros k lh. induction lh as [vs0 es0 | k vs0 n es0 lh IH es0'];
  intros vs j Hc Htr; destruct Htr as [k2 [lh2 Heq]];
  destruct lh2 as [vs1 es1 | k2' vs1 n1 es1 lh2 es1']; simpl in Heq;
  rewrite ? cat_split_at_e in Heq.
  - destruct (const_list_concat_inv
                (const_list_concat (v_to_e_const vs0) Hc)
                (v_to_e_const vs1) (not_const_br j) not_const_trap Heq)
      as [_ [Habs _]]. discriminate Habs.
  - destruct (const_list_concat_inv
                (const_list_concat (v_to_e_const vs0) Hc)
                (v_to_e_const vs1) (not_const_br j)
                (not_const_label n1 es1 (lfill lh2 [AI_trap])) Heq)
      as [_ [Habs _]]. discriminate Habs.
  - destruct (const_list_concat_inv
                (v_to_e_const vs0) (v_to_e_const vs1)
                (not_const_label n es0 (lfill lh (vs ++ [AI_basic (BI_br j)])))
                not_const_trap Heq)
      as [_ [Habs _]]. discriminate Habs.
  - destruct (const_list_concat_inv
                (v_to_e_const vs0) (v_to_e_const vs1)
                (not_const_label n es0 (lfill lh (vs ++ [AI_basic (BI_br j)])))
                (not_const_label n1 es1 (lfill lh2 [AI_trap])) Heq)
      as [_ [Habs _]]. injection Habs as _ _ Hin.
    apply (IH vs j Hc). exists k2', lh2. exact Hin.
Qed.

(* ── Inverting a trap through a context ───────────────────────────
   The lemmas below say where the trap of a trapping list can sit once
   the list is a filled context: never in the context's constant prefix,
   so either the hole is all values or the hole is itself trapping. *)

Lemma cat_split_at_cons : forall (a b : list administrative_instruction) e r c,
  seq.cat a (seq.cat (b ++ e :: r) c) = seq.cat (seq.cat a b) (e :: seq.cat r c).
Proof.
  intros a b e r c. induction a as [| x a IH]; simpl.
  - induction b as [| y b IHb]; simpl;
    [ reflexivity | rewrite IHb; reflexivity ].
  - rewrite IH; reflexivity.
Qed.

Lemma const_cons_head : forall e es,
  is_true (const_list (e :: es)) -> is_true (is_const e).
Proof.
  intros e es H. rewrite const_list_cons in H.
  apply Bool.andb_true_iff in H. destruct H as [H _]. exact H.
Qed.

Lemma is_const_v_to_e : forall v, is_true (is_const (v_to_e v)).
Proof.
  intros v. exact (const_cons_head _ _ (v_to_e_const [v])).
Qed.

(* Splitting a list that is not all values at its first non-value. *)
Lemma split_first_nonconst : forall es,
  const_list es = false ->
  exists c e r, es = c ++ e :: r /\ is_true (const_list c) /\ is_const e = false.
Proof.
  intros es. induction es as [| x es IH]; intros H.
  - discriminate H.
  - rewrite const_list_cons in H.
    destruct (is_const x) eqn:Hx; simpl in H.
    + destruct (IH H) as [c [e [r [Heq [Hc He]]]]].
      exists (x :: c), e, r. split; [ rewrite Heq; reflexivity | split; [| exact He ]].
      rewrite const_list_cons. rewrite Hx. exact Hc.
    + exists nil, x, es. split; [ reflexivity | split; [ reflexivity | exact Hx ]].
Qed.

Lemma trapping_not_const : forall es,
  trapping es -> is_true (const_list es) -> False.
Proof.
  intros es [k [lh Heq]] Hc. subst es.
  destruct lh as [vs0 es0 | k vs0 n es0 lh es0']; simpl in Hc;
  apply const_list_split in Hc as [_ Hc].
  - apply not_const_trap. exact (const_cons_head _ _ Hc).
  - apply (not_const_label n es0 (lfill lh [AI_trap])).
    exact (const_cons_head _ _ Hc).
Qed.

Lemma trapping_label_inv : forall n a b, trapping [AI_label n a b] -> trapping b.
Proof.
  intros n a b [k [lh Heq]].
  destruct lh as [vs0 es0 | k vs0 n0 es0 lh es0']; simpl in Heq;
  destruct vs0 as [| v vs0]; simpl in Heq.
  - injection Heq as Habs _. discriminate Habs.
  - injection Heq as Habs _. exfalso. apply (not_const_label n a b).
    rewrite Habs. apply is_const_v_to_e.
  - injection Heq as _ _ Hin _. exists k, lh. exact Hin.
  - injection Heq as Habs _. exfalso. apply (not_const_label n a b).
    rewrite Habs. apply is_const_v_to_e.
Qed.

Lemma lfill_const_inv : forall k (lh : lholed k) X,
  is_true (const_list (lfill lh X)) -> is_true (const_list X).
Proof.
  intros k lh. induction lh as [vs0 es0 | k vs0 n es0 lh IH es0'];
  intros X Hc; simpl in Hc; apply const_list_split in Hc as [_ Hc].
  - apply const_list_split in Hc as [Hc _]. exact Hc.
  - exfalso. apply (not_const_label n es0 (lfill lh X)).
    exact (const_cons_head _ _ Hc).
Qed.

Lemma trapping_lfill_inv : forall k (lh : lholed k) X,
  trapping (lfill lh X) -> is_true (const_list X) \/ trapping X.
Proof.
  intros k lh. induction lh as [vs0 es0 | k vs0 n es0 lh IH es0'];
  intros X Htr; destruct Htr as [k2 [lh2 Heq]]; simpl in Heq.
  - destruct (const_list X) eqn:HcX; [ left; reflexivity |]. right.
    destruct (split_first_nonconst X HcX) as [c [e [r [HXeq [Hc He]]]]].
    assert (HeN : ~ is_true (is_const e)). { rewrite He. discriminate. }
    destruct (const_es_exists Hc) as [cvs Hcvs].
    rewrite HXeq in Heq. rewrite cat_split_at_cons in Heq.
    destruct lh2 as [vs1 es1 | k2' vs1 n1 es1 lh2 es1']; simpl in Heq.
    + destruct (const_list_concat_inv
                  (const_list_concat (v_to_e_const vs0) Hc)
                  (v_to_e_const vs1) HeN not_const_trap Heq) as [_ [Hee _]].
      exists 0, (LH_base cvs r). simpl.
      rewrite HXeq. rewrite Hcvs. rewrite Hee. reflexivity.
    + destruct (const_list_concat_inv
                  (const_list_concat (v_to_e_const vs0) Hc)
                  (v_to_e_const vs1) HeN
                  (not_const_label n1 es1 (lfill lh2 [AI_trap])) Heq)
        as [_ [Hee _]].
      exists (S k2'), (LH_rec cvs n1 es1 lh2 r). simpl.
      rewrite HXeq. rewrite Hcvs. rewrite Hee. reflexivity.
  - destruct lh2 as [vs1 es1 | k2' vs1 n1 es1 lh2 es1']; simpl in Heq.
    + exfalso. destruct (const_list_concat_inv
                  (v_to_e_const vs0) (v_to_e_const vs1)
                  (not_const_label n es0 (lfill lh X)) not_const_trap Heq)
        as [_ [Habs _]]. discriminate Habs.
    + destruct (const_list_concat_inv
                  (v_to_e_const vs0) (v_to_e_const vs1)
                  (not_const_label n es0 (lfill lh X))
                  (not_const_label n1 es1 (lfill lh2 [AI_trap])) Heq)
        as [_ [Hlab _]]. injection Hlab as _ _ Hin.
      apply IH. exists k2', lh2. exact Hin.
Qed.

(* Stepping the hole preserves the context's obligations.  The branch-free
   and hazard-free disjuncts are taken apart by es_br_lfill /
   es_hazard_lfill and put back; the live-out disjunct does not mention the
   hole at all; and a step that drops a trap into the hole moves the body
   into the trapping disjunct instead.  The reduce derivation is needed for
   that last case only: a body that has already trapped stays trapped,
   because a reducible hole in it is either the trap itself or lies to the
   trap's right. *)
Lemma lh_labels_ok_step_gen : forall k (lh : lholed k) es es' K,
  lh_labels_ok lh es K ->
  (es_br es = false -> es_br es' = false) ->
  ((es_hazard es = false -> es_hazard es' = false) \/ trapping es') ->
  (forall kk (lhx : lholed kk), trapping (lfill lhx es) -> trapping (lfill lhx es')) ->
  lh_labels_ok lh es' K.
Proof.
  intros k lh. induction lh as [vs es0 | k vs n es0 lh IH es1];
  intros es es' K Hok Hb Hw Htr; simpl in *; [exact I |].
  destruct Hok as [Hlab Hrest]. split; [| eapply IH; eassumption ].
  destruct Hlab as [Hbr | [Hhaz | [Hdead | Ht]]];
  [| | right; right; left; exact Hdead
   | right; right; right; apply Htr; exact Ht ].
  - left. rewrite es_br_lfill in Hbr. rewrite es_br_lfill.
    apply Bool.orb_false_iff in Hbr. destruct Hbr as [Hlhb Hesb].
    rewrite Hlhb. rewrite (Hb Hesb). reflexivity.
  - destruct Hw as [Hfree | Htrap].
    + right. left. rewrite es_hazard_lfill in Hhaz. rewrite es_hazard_lfill.
      apply Bool.orb_false_iff in Hhaz. destruct Hhaz as [Hlhh Hesh].
      rewrite Hlhh. rewrite (Hfree Hesh). reflexivity.
    + right. right. right. apply trapping_lfill. exact Htrap.
Qed.

Inductive rel_lh (phi : local_map) : forall k, (N -> Prop) -> lholed k -> lholed k -> Prop :=
| rel_lh_base : forall K vs es' es'_o,
    rel_es phi K es' es'_o ->
    rel_lh phi 0 K (LH_base vs es') (LH_base vs es'_o)
| rel_lh_rec : forall k K vs n es' es'_o (lh lh_o : lholed k) es'' es''_o,
    rel_es phi (live_ext es'' K) es' es'_o ->
    rel_lh phi k (fun i => es_live_b i es' = true \/ live_ext es'' K i) lh lh_o ->
    rel_es phi K es'' es''_o ->
    rel_lh phi (S k) K (LH_rec vs n es' lh es'') (LH_rec vs n es'_o lh_o es''_o).

Lemma rel_es_lfill : forall phi k (lh lh_o : lholed k) K es es_o,
  rel_lh phi k K lh lh_o ->
  lh_labels_ok lh es K ->
  rel_es phi (lh_K lh K) es es_o ->
  rel_es phi K (lfill lh es) (lfill lh_o es_o).
Proof.
  intros phi k lh lh_o K es es_o Hlh. revert es es_o.
  induction Hlh as [ K vs es' es'_o He
                   | k K vs n es' es'_o lh lh_o es'' es''_o Ha Hlh IH Hb ];
  intros esx esx_o Hhole Hes; simpl in *.
  - apply rel_es_app; [ apply rel_es_v_to_e_list |].
    apply rel_es_app; [ exact Hes | exact He ].
  - apply rel_es_app; [ apply rel_es_v_to_e_list |].
    change (rel_es phi K (AI_label n es' (lfill lh esx) :: es'')
                         (AI_label n es'_o (lfill lh_o esx_o) :: es''_o)).
    apply rel_cons; [| exact Hb ].
    destruct Hhole as [Hlab Hrest].
    apply rel_label.
    + exact Hlab.
    + eapply rel_es_weaken; [ exact Ha |]. intros i Hi. exact Hi.
    + apply IH; [ exact Hrest | exact Hes ].
Qed.

(* The converse: the relation at a filled context determines a filled
   context on the other side, with the hole related under lh_K. *)
Lemma rel_es_lfill_inv : forall phi k (lh : lholed k) K es X,
  rel_es phi K (lfill lh es) X ->
  exists (lh_o : lholed k) es_o,
    X = lfill lh_o es_o /\
    rel_lh phi k K lh lh_o /\
    lh_labels_ok lh es K /\
    rel_es phi (lh_K lh K) es es_o.
Proof.
  intros phi k lh. induction lh as [ vs es' | k vs n es' lh IH es'' ];
  intros K es X H; simpl in H.
  - apply rel_es_split in H. destruct H as [X0 [X1 [Heq [H0 H1]]]].
    apply rel_es_v_to_e_list_inv in H0. subst X0.
    apply rel_es_split in H1. destruct H1 as [Xh [Xt [Heq1 [Hh Ht]]]].
    exists (LH_base vs Xt), Xh. split; [| split; [| split]].
    + simpl. rewrite Heq. rewrite Heq1. reflexivity.
    + apply rel_lh_base. exact Ht.
    + exact I.
    + exact Hh.
  - apply rel_es_split in H. destruct H as [X0 [X1 [Heq [H0 H1]]]].
    apply rel_es_v_to_e_list_inv in H0. subst X0.
    change (rel_es phi K (AI_label n es' (lfill lh es) :: es'') X1) in H1.
    inversion H1 as [| phi' K' e0 e0_o t0 t0_o Hlab Htail Heq2 Heq3 Heq4 ]; subst.
    inversion Hlab as [| | | | | | phi'' K'' n'' a a_o b b_o Hlab' Ha Hb | ]; subst.
    destruct (IH (fun i => es_live_b i es' = true \/ live_ext es'' K i) es b_o Hb)
      as [lh_o [es_o [Heqb [Hlh [Hok Hhole]]]]].
    exists (LH_rec vs n a_o lh_o t0_o), es_o. split; [| split; [| split]].
    + simpl. rewrite Heqb. reflexivity.
    + apply rel_lh_rec; [ exact Ha | exact Hlh | exact Htail ].
    + simpl. split; [ exact Hlab' | exact Hok ].
    + exact Hhole.
Qed.

(* rs_trap needs to know that the optimized redex is not already a bare
   trap.  The relation preserves the context's shape, so a trivial
   optimized context forces a trivial source one.  Stated by induction on
   the derivation rather than on the context, to avoid destructing an
   index-constrained lholed. *)
Lemma rel_lh_trap_inv : forall phi k K (lh lh_o : lholed k),
  rel_lh phi k K lh lh_o ->
  lfill lh_o [AI_trap] = [AI_trap] -> lfill lh [AI_trap] = [AI_trap].
Proof.
  intros phi k K lh lh_o H.
  induction H; intros Habs; simpl in *.
  - destruct vs as [|v0 vs0]; simpl in *.
    + destruct es'_o as [|z zs]; simpl in Habs.
      * match goal with
        | Hx : rel_es _ _ _ nil |- _ => rewrite (rel_es_nil_inv_r _ _ _ Hx)
        end. reflexivity.
      * exfalso. injection Habs as Hz. discriminate Hz.
    + exfalso. destruct v0 as [ | | r0]; simpl in Habs; try discriminate Habs.
      destruct r0; simpl in Habs; discriminate Habs.
  - destruct vs as [|v0 vs0]; simpl in Habs.
    + discriminate Habs.
    + exfalso. destruct v0 as [ | | r0]; simpl in Habs; try discriminate Habs.
      destruct r0; simpl in Habs; discriminate Habs.
Qed.

Section Correctness.

Context `{hfc : host_function_class} `{memory : BlockUpdateMemory} `{ho : host}.

(* ── reduce never introduces a write ──────────────────────────────────
   Needed to re-establish rel_label after a step inside a label body: the
   body must still be write-free afterwards.  Every result is built from
   values, traps, the redex's own sub-lists, or a frame -- and ai_writes of
   a frame is false, since a callee's writes belong to its own activation. *)

Lemma es_writes_cons : forall e es,
  es_writes (e :: es) = ai_writes e || es_writes es.
Proof. reflexivity. Qed.

Lemma const_list_nowrite : forall es,
  is_true (const_list es) -> es_writes es = false.
Proof.
  intros l. induction l as [|e l' IH]; intros Hc; simpl; [reflexivity |].
  simpl in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
  rewrite (IH H2). rewrite Bool.orb_false_r.
  destruct e; simpl in *; try reflexivity; try discriminate H1.
  destruct b; simpl in *; try reflexivity; try discriminate H1.
Qed.

Lemma es_writes_cat : forall es1 es2,
  es_writes (seq.cat es1 es2) = es_writes es1 || es_writes es2.
Proof.
  intros es1. induction es1 as [|e es1' IH]; intros es2; simpl.
  - reflexivity.
  - rewrite IH. apply Bool.orb_assoc.
Qed.

Lemma ai_writes_v_to_e : forall v, ai_writes (v_to_e v) = false.
Proof.
  intros v. destruct v as [ | | vr]; simpl; try reflexivity. destruct vr; reflexivity.
Qed.

Lemma es_writes_result_to_stack : forall r, es_writes (result_to_stack r) = false.
Proof.
  intros r. destruct r; simpl; [ apply es_writes_v_to_e_list | reflexivity ].
Qed.

Lemma es_br_cons : forall e es, es_br (e :: es) = ai_br e || es_br es.
Proof. reflexivity. Qed.

Lemma const_list_nobr : forall es,
  is_true (const_list es) -> es_br es = false.
Proof.
  intros l. induction l as [|e l' IH]; intros Hc; simpl; [reflexivity |].
  simpl in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
  rewrite (IH H2). rewrite Bool.orb_false_r.
  destruct e; simpl in *; try reflexivity; try discriminate H1.
  destruct b; simpl in *; try reflexivity; try discriminate H1.
Qed.

Lemma es_br_cat : forall es1 es2,
  es_br (seq.cat es1 es2) = es_br es1 || es_br es2.
Proof. exact es_br_app. Qed.

Lemma ai_br_v_to_e : forall v, ai_br (v_to_e v) = false.
Proof.
  intros v. destruct v as [ | | vr]; simpl; try reflexivity. destruct vr; reflexivity.
Qed.

Lemma es_br_result_to_stack : forall r, es_br (result_to_stack r) = false.
Proof.
  intros r. destruct r; simpl; [ apply es_br_v_to_e_list | reflexivity ].
Qed.

Ltac nobr_simp Hw :=
  rewrite ? es_br_app in Hw |- *;
  rewrite ? es_br_cat in Hw |- *;
  rewrite ? es_br_cons in Hw |- *;
  rewrite ? ai_br_label in Hw |- *;
  rewrite ? es_br_v_to_e_list in Hw |- *;
  rewrite ? es_br_result_to_stack in Hw |- *;
  rewrite ? ai_br_v_to_e in Hw |- *;
  rewrite ? bs_br_to_e_list in Hw |- *;
  cbn [ai_br] in Hw |- *;
  rewrite ? bi_br_block in Hw |- *;
  rewrite ? bi_br_loop in Hw |- *;
  rewrite ? bi_br_if in Hw |- *;
  cbn [bi_br] in Hw |- *;
  rewrite ? Bool.orb_false_l in Hw |- *;
  rewrite ? Bool.orb_false_r in Hw |- *;
  rewrite ? Bool.orb_diag in Hw |- *;
  repeat (apply Bool.orb_false_iff in Hw; destruct Hw as [? Hw]);
  try reflexivity; try assumption; try discriminate Hw;
  try (solve [ apply const_list_nobr; assumption ]).

Lemma reduce_simple_nobr : forall es es',
  reduce_simple es es' -> es_br es = false -> es_br es' = false.
Proof.
  intros es es' H. induction H; intros Hw; nobr_simp Hw.
  (* rs_br cannot fire on a branch-free redex: the hole holds a br *)
  exfalso.
  match goal with
  | Hl : lfill ?lhx _ = ?LI, Hb : es_br ?LI = false |- _ =>
      rewrite <- Hl in Hb; eapply es_br_no_br; exact Hb
  end.
Qed.

Ltac nowrite_simp Hw :=
  rewrite ? es_writes_app in Hw |- *;
  rewrite ? es_writes_cat in Hw |- *;
  rewrite ? es_writes_cons in Hw |- *;
  rewrite ? ai_writes_label in Hw |- *;
  rewrite ? es_writes_v_to_e_list in Hw |- *;
  rewrite ? es_writes_result_to_stack in Hw |- *;
  rewrite ? ai_writes_v_to_e in Hw |- *;
  rewrite ? bs_writes_to_e_list in Hw |- *;
  cbn [ai_writes] in Hw |- *;
  rewrite ? bi_writes_block in Hw |- *;
  rewrite ? bi_writes_loop in Hw |- *;
  rewrite ? bi_writes_if in Hw |- *;
  cbn [bi_writes] in Hw |- *;
  rewrite ? Bool.orb_false_l in Hw |- *;
  rewrite ? Bool.orb_false_r in Hw |- *;
  rewrite ? Bool.orb_diag in Hw |- *;
  repeat (apply Bool.orb_false_iff in Hw; destruct Hw as [? Hw]);
  try reflexivity; try assumption; try discriminate Hw;
  try (solve [ apply const_list_nowrite; assumption ]).

Lemma reduce_simple_nowrite : forall es es',
  reduce_simple es es' -> es_writes es = false -> es_writes es' = false.
Proof.
  intros es es' H. induction H; intros Hw; nowrite_simp Hw.
  (* rs_br: the branch continuation and the values are both write-free *)
  rewrite (const_list_nowrite vs H). rewrite H2. reflexivity.
Qed.

(* [store_guarded] is in toplevel_spec.v, since it survives all the way into
   the statement of the top-level theorem.  Callee bodies come from the
   store, so the nesting restriction has to hold there too: r_invoke_native
   relates a fresh activation to itself under empty, which needs rel_bs_refl
   on the callee's body. *)

(* Kept as a lemma rather than inlined so that the tactic below has one
   place to aim at. *)
Lemma frames_agree_sub : forall phi K K' f f_o,
  (forall i, K' i -> K i) ->
  frames_agree phi K f f_o -> frames_agree phi K' f f_o.
Proof. exact frames_agree_mono. Qed.

Lemma reduce_nowrite : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' -> es_writes es = false -> es_writes es' = false.
Proof.
  intros hs s f es hs' s' f' es' H. induction H; intros Hw; nowrite_simp Hw.
  - eapply reduce_simple_nowrite; eassumption.
  - (* r_block: the body is the block's own, and vs are values *)
    rewrite es_writes_cat. rewrite bs_writes_to_e_list.
    rewrite H4. rewrite Hw. reflexivity.
  - (* r_loop: likewise, plus the loop instruction in the continuation *)
    rewrite es_writes_cons. rewrite es_writes_cat. rewrite bs_writes_to_e_list.
    cbn [ai_writes es_writes]. rewrite bi_writes_loop.
    rewrite H4. rewrite Hw. reflexivity.
  - (* r_label: the context contributes the same writes either way *)
    subst les les'. rewrite es_writes_lfill in Hw. rewrite es_writes_lfill.
    apply Bool.orb_false_iff in Hw. destruct Hw as [Hlh Hes].
    rewrite Hlh. rewrite (IHreduce Hes). reflexivity.
Qed.

(* Branch-freedom survives a step for the same reason write-freedom does:
   no rule builds a branch, they only move existing sub-lists around. *)
Lemma reduce_nobr : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' -> es_br es = false -> es_br es' = false.
Proof.
  intros hs s f es hs' s' f' es' H. induction H; intros Hw; nobr_simp Hw.
  - eapply reduce_simple_nobr; eassumption.
  - (* r_block *)
    rewrite es_br_cat. rewrite bs_br_to_e_list.
    rewrite H4. rewrite Hw. reflexivity.
  - (* r_loop: the continuation is the loop instruction itself *)
    rewrite es_br_cons. rewrite es_br_cat. rewrite bs_br_to_e_list.
    cbn [ai_br es_br]. rewrite bi_br_loop.
    rewrite H4. rewrite Hw. reflexivity.
  - (* r_label *)
    subst les les'. rewrite es_br_lfill in Hw. rewrite es_br_lfill.
    apply Bool.orb_false_iff in Hw. destruct Hw as [Hlh Hes].
    rewrite Hlh. rewrite (IHreduce Hes). reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════
   The forward simulation.
   ══════════════════════════════════════════════════════════════════ *)

(* The uniform case: the redex is values plus one local-free instruction,
   so the two sides are the same list, the same rule fires on the target
   after rewriting f_inst, and the live set is untouched. *)
Ltac sim_plain :=
  (* subst only the target list: a blanket subst also eliminates the rule's
     own defining equations, which its side conditions then need. *)
  match goal with
  | Hrel : rel_es _ _ _ ?eo |- _ =>
      apply rel_es_plain_inv in Hrel; [ subst eo | solve [plain_solve] ]
  end;
  match goal with
  | Hfr : frames_agree _ _ _ _ |- _ =>
      let Hinst := fresh "Hinst" in
      pose proof (proj1 Hfr) as Hinst;
      do 2 eexists; split; [| split];
      [ econstructor; rewrite <- ? Hinst; first [ eassumption | reflexivity ]
      | apply rel_es_plain; solve [plain_solve]
      | refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve ]
  end.

(* ── The two cases that carry the content ────────────────────────── *)

(* A read: the local is live here by construction (the instruction reads
   it), so the frame agreement applies and the target slot holds the same
   value. *)
Lemma sim_local_get : forall phi K f f_o hs s j v es_o,
  lookup_N (f_locs f) j = Some v ->
  rel_es phi K [AI_basic (BI_local_get j)] es_o ->
  frames_agree phi (live_ext [AI_basic (BI_local_get j)] K) f f_o ->
  exists f_o' es_o',
    reduce hs s f_o es_o hs s f_o' es_o' /\
    rel_es phi K [v_to_e v] es_o' /\
    frames_agree phi (live_ext [v_to_e v] K) f f_o'.
Proof.
  intros phi K f f_o hs s j v es_o H Hrel Hfr.
  apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
  apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
  apply rel_e_basic_inv in He. destruct He as [b_o [Heb Hb]]. subst e_o.
  apply rel_b_get_inv in Hb. subst b_o.
  destruct Hfr as [Hinst [Hlen [Hlenb HR]]].
  assert (Hj : N.to_nat j < length (f_locs f)).
  { apply (proj1 (nth_error_Some (f_locs f) (N.to_nat j))).
    intro Hnone. unfold lookup_N in H. rewrite H in Hnone. discriminate Hnone. }
  assert (Hnth : nth_error (f_locs f) (N.to_nat j)
                 = nth_error (f_locs f_o) (N.to_nat (apply_phi_local phi j))).
  { apply HR; [ exact Hj |]. left. simpl. rewrite N.eqb_refl. reflexivity. }
  exists f_o, [v_to_e v]. split; [| split].
  - apply r_local_get. unfold lookup_N. rewrite <- Hnth. exact H.
  - apply rel_cons; [ apply rel_e_v_to_e | apply rel_nil ].
  - split; [ exact Hinst | split; [ exact Hlen | split; [ exact Hlenb |]]].
    intros i Hi HL. apply HR; [ exact Hi |].
    right. split; [ reflexivity |].
    apply (live_ext_neutral [v_to_e v] K i); [ solve [neutral_solve] | exact HL ].
Qed.

(* A write: this is where R_phi_live_set is discharged, and its side
   condition -- after writing i, no other still-readable local shares i's
   slot -- is exactly the slot_free the relation carries at this
   instruction.  Note the local being written is *dead* here (its own write
   kills it), which is why the target's slot must be known in range from
   the length component rather than from the agreement. *)
Lemma sim_local_set : forall phi K f f' f_o hs s i v vd es_o,
  f_inst f' = f_inst f ->
  N.to_nat i < length (f_locs f) ->
  f_locs f' = seq.set_nth vd (f_locs f) (N.to_nat i) v ->
  rel_es phi K [v_to_e v; AI_basic (BI_local_set i)] es_o ->
  frames_agree phi (live_ext [v_to_e v; AI_basic (BI_local_set i)] K) f f_o ->
  exists f_o' es_o',
    reduce hs s f_o es_o hs s f_o' es_o' /\
    rel_es phi K [] es_o' /\
    frames_agree phi (live_ext [] K) f' f_o'.
Proof.
  intros phi K f f' f_o hs s i v vd es_o Hinst' Hi Hlocs' Hrel Hfr.
  apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
  apply rel_e_v_inv in He. subst e_o.
  apply rel_es_cons_inv in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
  apply rel_es_nil_inv in Ht1. subst t1. subst t_o. subst es_o.
  apply rel_e_basic_inv in He1. destruct He1 as [b_o [Hb1 Hb]]. subst e1.
  apply rel_b_set_inv in Hb. destruct Hb as [Hbo Hsf]. subst b_o.
  destruct Hfr as [Hinst [Hlen [Hlenb HR]]].
  assert (Hpi : N.to_nat (apply_phi_local phi i) < length (f_locs f_o))
    by (apply Hlen; exact Hi).
  exists (Build_frame (seq.set_nth vd (f_locs f_o)
                         (N.to_nat (apply_phi_local phi i)) v) (f_inst f_o)), nil.
  split; [| split].
  - eapply r_local_set with (vd := vd); [ reflexivity | | reflexivity ].
    simpl. apply lt_to_leq. exact Hpi.
  - apply rel_nil.
  - split; [| split; [| split]].
    + simpl. rewrite Hinst'. exact Hinst.
    + simpl. rewrite Hlocs'.
      rewrite (length_set_nth_lt vd (f_locs f) (N.to_nat i) v Hi).
      rewrite (length_set_nth_lt vd (f_locs f_o)
                 (N.to_nat (apply_phi_local phi i)) v Hpi).
      exact Hlen.
    + simpl. rewrite Hlocs'.
      rewrite (length_set_nth_lt vd (f_locs f) (N.to_nat i) v Hi).
      rewrite (length_set_nth_lt vd (f_locs f_o)
                 (N.to_nat (apply_phi_local phi i)) v Hpi).
      exact Hlenb.
    + simpl. rewrite Hlocs'.
      eapply R_phi_live_set; [ | | exact Hi | exact Hpi | exact HR ].
      * intros j HL' Hne. apply Hsf; [ exact HL' | exact Hne ].
      * intros j HL' Hne. right. split; [| apply (live_ext_nil K j); exact HL' ].
        simpl. destruct (live_v_to_e j v) as [_ Hk]. rewrite Hk. simpl.
        rewrite Bool.orb_false_r.
        destruct (N.eqb_spec j i) as [Heq | Hne2];
        [ exfalso; apply Hne; exact Heq | reflexivity ].
Qed.

Definition is_complex_basic (b : basic_instruction) : bool :=
  match b with
  | BI_local_get _ | BI_local_set _ | BI_local_tee _
  | BI_block _ _ | BI_loop _ _ | BI_if _ _ _ => true
  | _ => false
  end.

Lemma apply_phi_preserves : forall phi b target,
  apply_phi phi b = target ->
  is_complex_basic target = false ->
  b = target.
Proof.
  intros phi b target H Hc.
  destruct b; simpl in H;
  try exact H;
  try (rewrite <- H in Hc; simpl in Hc; discriminate Hc).
Qed.

(* ── call-transport: replay a bare call step on a same-instance frame ── *)

Lemma app_singleton_inv : forall A (l1 l2 : list A) z,
  l1 ++ l2 = [z] -> (l1 = [] /\ l2 = [z]) \/ (l1 = [z] /\ l2 = []).
Proof.
  intros A l1 l2 z H.
  destruct l1 as [|a1 l1'].
  - left. split; [reflexivity | exact H].
  - right.
    simpl in H.
    injection H as Ha Htail.
    destruct l1'; simpl in Htail; try discriminate Htail.
    split; [subst a1; reflexivity | exact Htail].
Qed.

Lemma v_to_e_not_basic_call : forall v i, v_to_e v <> AI_basic (BI_call i).
Proof.
  intros v i H.
  destruct v as [n | vv | r]; simpl in H; try discriminate H.
  destruct r; simpl in H; discriminate H.
Qed.

Lemma cat_nil : forall A (l1 l2 : list A), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros A l1 l2 H. destruct l1 as [|a l1']; [split; [reflexivity | exact H] | simpl in H; discriminate H].
Qed.

(* Inverting a lfill that produces a singleton [AI_basic (BI_call i)] /
   [AI_invoke a]: the raw body equals the filled list. *)
Lemma lfill_singleton_call_inv : forall {k} (lh : lholed k) es es' i a,
  lfill lh es = [AI_basic (BI_call i)] ->
  lfill lh es' = [AI_invoke a] ->
  es = [AI_basic (BI_call i)] /\ es' = [AI_invoke a].
Proof.
  induction lh as [vs es'' | k0 vs' n' es_in' lh' IH es_out']; intros es es' i a H H0.
  - (* LH_base: v_to_e_list vs ++ es ++ es'' *)
    simpl in H, H0.
    destruct vs as [|v0 vs0].
    + (* vs = [] *)
      simpl in H, H0.
      destruct es as [|e es1].
      * (* es = [] : es'' = [AI_basic (BI_call i)] *)
        cbv in H.
        rewrite H in H0.
        apply app_singleton_inv in H0.
        destruct H0 as [[Hes' Hbad] | [Hes' Hbad]]; discriminate Hbad.
      * (* es = e :: es1 : e = AI_basic (BI_call i), es1 ++ es'' = [] *)
        simpl in H.
        injection H as He Ht.
        destruct (@cat_nil _ es1 es'' Ht) as [Hes1 Hes''].
        subst es1 es''.
        destruct es' as [|d es2]; simpl in H0.
        -- discriminate H0.
        -- injection H0 as Hd Ht'.
           destruct (@cat_nil _ es2 [] Ht') as [He2a He2b].
           subst es2 d.
           subst e. split; reflexivity.
    + (* vs = v0 :: vs0: v_to_e v0 = AI_basic (BI_call i) *)
      simpl in H.
      injection H as Hv Ht.
      exfalso. eapply v_to_e_not_basic_call. exact Hv.
  - (* LH_rec: contains an AI_label *)
    simpl in H.
    destruct vs' as [|v0 vs0'].
    + cbv in H.
      injection H as Hz _; discriminate Hz.
    + cbv in H.
      injection H as Hv _.
      exfalso. eapply v_to_e_not_basic_call. exact Hv.
Qed.

(* A single call step replay on a frame with the same instance. *)
(* The target store is arbitrary: r_call reads the instance, not the
   store, and every other rule is excluded by the shape of the list. *)
Lemma reduce_call_transport : forall hs s f i a s2 f_src,
  reduce hs s f [AI_basic (BI_call i)] hs s f [AI_invoke a] ->
  f_inst f_src = f_inst f ->
  reduce hs s2 f_src [AI_basic (BI_call i)] hs s2 f_src [AI_invoke a].
Proof.
  intros hs s f i a s2 f_src Hred.
  revert s2 f_src.
  remember [AI_basic (BI_call i)] as e eqn:He.
  remember [AI_invoke a] as e' eqn:He'.
  induction Hred; intros s2 f_src Hinst; try (inversion He).
  - apply r_simple. rewrite He in H. exact H.
  - destruct vs as [|v vs']; cbv in He.
    + congruence.  (* r_block *)
    + injection He as Hv Ht; destruct vs' as [|w vs'']; simpl in Ht; discriminate Ht.
  - destruct vs as [|v vs']; cbv in He.
    + congruence.  (* r_loop *)
    + injection He as Hv Ht; destruct vs' as [|w vs'']; simpl in Ht; discriminate Ht.
  - subst i0. apply r_call. rewrite <- Hinst in H. exact H.  (* r_call *)
  - destruct ves as [|v ves']; cbv in He.  (* r_invoke_native *)
    + congruence.
    + injection He as Hv Ht; destruct ves' as [|w ves'']; simpl in Ht; discriminate Ht.
  - destruct ves as [|v ves']; cbv in He.  (* r_invoke_host_success *)
    + congruence.
    + injection He as Hv Ht; destruct ves' as [|w ves'']; simpl in Ht; discriminate Ht.
  - destruct ves as [|v ves']; cbv in He.  (* r_invoke_host_diverge *)
    + congruence.
    + injection He as Hv Ht; destruct ves' as [|w ves'']; simpl in Ht; discriminate Ht.
  - rewrite He in H. rewrite He' in H0.  (* r_label *)
    destruct (lfill_singleton_call_inv lh es es' i a H H0) as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hinst].
Qed.

(* Call-indirect transports: replay a call_indirect step on a same-instance frame. *)
Lemma reduce_call_indirect_success_transport :
  forall hs s f v x y a f_src,
    reduce hs s f [v_to_e v; AI_basic (BI_call_indirect x y)] hs s f [AI_invoke a] ->
    f_inst f_src = f_inst f ->
    reduce hs s f_src [v_to_e v; AI_basic (BI_call_indirect x y)] hs s f_src [AI_invoke a].
Proof.
  intros hs s f v x y a f_src Hred.
  revert f_src.
  remember [v_to_e v; AI_basic (BI_call_indirect x y)] as e eqn:He.
  remember [AI_invoke a] as e' eqn:He'.
  induction Hred; intros f_src Hinst; try (inversion He); try (discriminate He').
  - apply r_simple. rewrite He in H. exact H.
  - subst x0 y0. eapply r_call_indirect_success;
      [rewrite <- Hinst in H; exact H | exact H0 | rewrite <- Hinst in H1; exact H1].
  - assert (Hin : In (AI_invoke a0) [v_to_e v; AI_basic (BI_call_indirect x y)]).
  { rewrite <- He. apply in_or_app. right. left. reflexivity. }
  simpl in Hin.
  destruct Hin as [Hv | Hinv].
  - destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
    destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
  - destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs]. (* r_invoke_host_success *)
  - rewrite He in H. rewrite He' in H0.  (* r_label *)
    assert (Hfill : es = [v_to_e v; AI_basic (BI_call_indirect x y)] /\ es' = [AI_invoke a]).
    { eapply lfill_singleton_invert; [exact H | exact H0 | | ].
      { intro Hm. destruct v as [vn | vv | r]; compute in Hm; try discriminate Hm.
        destruct r as [t | fa | ea]; compute in Hm; discriminate Hm. }
      { intro Hc. cbv in Hc. discriminate Hc. } }
    destruct Hfill as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hinst].
Qed.

Lemma reduce_call_indirect_failure_transport :
  forall hs s f v x y f_src,
    reduce hs s f [v_to_e v; AI_basic (BI_call_indirect x y)] hs s f [AI_trap] ->
    f_inst f_src = f_inst f ->
    reduce hs s f_src [v_to_e v; AI_basic (BI_call_indirect x y)] hs s f_src [AI_trap].
Proof.
  intros hs s f v x y f_src Hred.
  revert f_src.
  remember [v_to_e v; AI_basic (BI_call_indirect x y)] as e eqn:He.
  remember [AI_trap] as e' eqn:He'.
  induction Hred; intros f_src Hinst; try (inversion He); try (discriminate He').
  - apply r_simple. rewrite He in H. exact H.
  - subst x0 y0. eapply r_call_indirect_failure_mismatch;
      [rewrite <- Hinst in H; exact H | exact H0 | rewrite <- Hinst in H1; exact H1].
  - subst x0 y0. eapply r_call_indirect_failure_bound; rewrite <- Hinst in H; exact H.
  - subst x0 y0. eapply r_call_indirect_failure_null_ref; rewrite <- Hinst in H; exact H.
  - assert (Hin : In (AI_invoke a) [v_to_e v; AI_basic (BI_call_indirect x y)]).
  { rewrite <- He. apply in_or_app. right. left. reflexivity. }
  simpl in Hin.
  destruct Hin as [Hv | Hinv].
  - destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
    destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
  - destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs]. (* r_invoke_host_success *)
  - assert (Hin : In (AI_invoke a) [v_to_e v; AI_basic (BI_call_indirect x y)]).
  { rewrite <- He. apply in_or_app. right. left. reflexivity. }
  simpl in Hin.
  destruct Hin as [Hv | Hinv].
  - destruct v as [n1 | vv | r1]; simpl in Hv; try discriminate Hv;
    destruct r1 as [t | fa | ea]; simpl in Hv; discriminate Hv.
  - destruct Hinv as [Hv2 | Habs]; [discriminate Hv2 | exfalso; exact Habs]. (* r_invoke_host_diverge *)
  - rewrite He in H. rewrite He' in H0.  (* r_label *)
    assert (Hfill : es = [v_to_e v; AI_basic (BI_call_indirect x y)] /\ es' = [AI_trap]).
    { eapply lfill_singleton_invert; [exact H | exact H0 | | ].
      { intro Hm. destruct v as [vn | vv | r]; compute in Hm; try discriminate Hm.
        destruct r as [t | fa | ea]; compute in Hm; discriminate Hm. }
      { intro Hc. cbv in Hc. discriminate Hc. } }
    destruct Hfill as [Hes Hes'].
    subst. eapply IHHred; [reflexivity | reflexivity | exact Hinst].
Qed.

(* ── Hazards and traps across a step ──────────────────────────────
   A step either introduces no new hazard, or it has trapped: every rule
   that produces AI_trap produces exactly [AI_trap], and r_label wraps
   that in a context, which is still a trapping list.  This is what keeps
   label_ok alive across r_label -- see the note below sim_simple. *)
Lemma trapping_trap : trapping [AI_trap].
Proof. exists 0, (LH_base nil nil). reflexivity. Qed.

Ltac hz_zero :=
  solve [ repeat first
    [ reflexivity
    | rewrite es_hazard_app
    | rewrite es_hazard_v_to_e_list
    | rewrite es_hazard_to_e_list
    | rewrite ai_hazard_v_to_e
    | (rewrite es_hazard_const; [| assumption])
    | cbn [es_hazard ai_hazard bi_writes] ] ].

Lemma reduce_simple_hazard_or_trap : forall es es',
  reduce_simple es es' ->
  (es_hazard es = false -> es_hazard es' = false) \/ trapping es'.
Proof.
  intros es es' Hred. induction Hred.
  all: try (solve [ left; intros _; hz_zero ]).
  all: try (solve [ right; exact trapping_trap ]).
  (* the two ifs: the block that is entered writes no more than the if *)
  1-2: left; intros Hz;
       cbn [es_hazard ai_hazard] in Hz |- *;
       rewrite bi_writes_if in Hz; rewrite bi_writes_block;
       cbn [bi_writes] in Hz;
       rewrite Bool.orb_false_l in Hz; rewrite Bool.orb_false_r in Hz;
       rewrite Bool.orb_false_r;
       apply Bool.orb_false_iff in Hz; destruct Hz as [H1 H2];
       solve [ exact H1 | exact H2 ].
  { (* rs_br: what is left is the label's continuation, which the label
       already accounted for *)
    left; intros Hz. rewrite es_hazard_cat.
    cbn [es_hazard] in Hz. rewrite ai_hazard_label in Hz.
    rewrite Bool.orb_false_r in Hz.
    apply Bool.orb_false_iff in Hz. destruct Hz as [Ha _].
    rewrite es_hazard_const; [| assumption ].
    rewrite Ha. reflexivity. }
  { (* rs_local_tee: the tee is itself a write, so the premise is false *)
    left; intros Hz. exfalso.
    cbn [es_hazard ai_hazard] in Hz. rewrite ai_hazard_v_to_e in Hz.
    simpl in Hz. discriminate Hz. }
Qed.

Lemma reduce_hazard_or_trap : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  (es_hazard es = false -> es_hazard es' = false) \/ trapping es'.
Proof.
  intros hs s f es hs' s' f' es' Hred. induction Hred.
  all: try (solve [ left; intros _; hz_zero ]).
  all: try (solve [ right; exact trapping_trap ]).
  all: try (solve [ eapply reduce_simple_hazard_or_trap; eassumption ]).
  (* r_block and r_loop: entering a block moves its body, and nothing
     else, under a label; the loop's continuation is the loop itself *)
  1-2: left; intros Hz; rewrite es_hazard_cat in Hz;
       cbn [es_hazard ai_hazard] in Hz;
       cbn [es_hazard]; rewrite ai_hazard_label;
       rewrite ! es_hazard_cat; rewrite es_hazard_to_e_list;
       cbn [es_hazard ai_hazard] in Hz |- *;
       rewrite ! Bool.orb_false_r in Hz; rewrite ! Bool.orb_false_r;
       first [ rewrite bi_writes_block in Hz | rewrite bi_writes_loop in Hz ];
       first [ rewrite bi_writes_loop | idtac ];
       apply Bool.orb_false_iff in Hz; destruct Hz as [Hv Hw];
       rewrite Hv; rewrite Hw; reflexivity.
  { (* the host call returns either values or a trap *)
    destruct r as [rvs |].
    - left. intros _. hz_zero.
    - right. exact trapping_trap. }
  { (* r_label *)
    subst les. subst les'.
    destruct IHHred as [Hfree | Htrap].
    - left. intros Hz. rewrite es_hazard_lfill in Hz. rewrite es_hazard_lfill.
      apply Bool.orb_false_iff in Hz. destruct Hz as [Hl Hh].
      rewrite Hl. rewrite (Hfree Hh). reflexivity.
    - right. apply trapping_lfill. exact Htrap. }
Qed.

(* ── A reducible list is never all values, and stays trapped ──────
   The two facts are proved together because they need the same case
   analysis: for all but a handful of rules the redex's first non-value
   instruction is neither a trap nor a label, which refutes both being
   all values and being trapping. *)
Fixpoint hd_nc (es : list administrative_instruction) : option administrative_instruction :=
  match es with
  | [] => None
  | e :: rest => if is_const e then hd_nc rest else Some e
  end.

Lemma hd_nc_cons_const : forall e es,
  is_true (is_const e) -> hd_nc (e :: es) = hd_nc es.
Proof. intros e es H. simpl. rewrite H. reflexivity. Qed.

Lemma hd_nc_app_const : forall ves es,
  is_true (const_list ves) -> hd_nc (ves ++ es) = hd_nc es.
Proof.
  intros ves. induction ves as [| v ves IH]; intros es H; simpl; [reflexivity |].
  rewrite const_list_cons in H. apply Bool.andb_true_iff in H.
  destruct H as [H1 H2]. rewrite H1. apply IH. exact H2.
Qed.

Lemma hd_nc_cat_const : forall ves es,
  is_true (const_list ves) -> hd_nc (seq.cat ves es) = hd_nc es.
Proof. exact hd_nc_app_const. Qed.

Lemma const_hd_nc : forall es, is_true (const_list es) -> hd_nc es = None.
Proof.
  intros es. induction es as [| e es IH]; intros H; [reflexivity |].
  rewrite const_list_cons in H. apply Bool.andb_true_iff in H.
  destruct H as [H1 H2]. simpl. rewrite H1. exact (IH H2).
Qed.

(* A list whose first non-value is an ordinary instruction is neither all
   values nor trapping: a trapping list has a trap or a label there. *)
Lemma nc_shape : forall es e,
  hd_nc es = Some e ->
  e <> AI_trap -> (forall n a b, e <> AI_label n a b) ->
  ~ is_true (const_list es) /\ ~ trapping es.
Proof.
  intros es e Hhd Htr Hlab. split.
  - intros Hc. rewrite (const_hd_nc es Hc) in Hhd. discriminate Hhd.
  - intros [k [lh Heq]]. subst es.
    destruct lh as [vs0 es0 | k vs0 n0 es0 lh es0'];
    rewrite hd_nc_cat_const in Hhd; try apply v_to_e_const;
    simpl in Hhd; injection Hhd as Hhd.
    + apply Htr. rewrite <- Hhd. reflexivity.
    + apply (Hlab n0 es0 (lfill lh [AI_trap])). rewrite <- Hhd. reflexivity.
Qed.

Ltac hd_solve :=
  repeat first [ (rewrite hd_nc_cat_const; [| assumption])
               | (rewrite hd_nc_app_const; [| assumption])
               | (rewrite hd_nc_cat_const; [| apply v_to_e_const])
               | (rewrite hd_nc_app_const; [| apply v_to_e_const])
               | (rewrite hd_nc_cons_const; [| apply is_const_v_to_e])
               | (rewrite hd_nc_cons_const; [| reflexivity]) ];
  reflexivity.

Ltac nc_auto :=
  match goal with
  | |- ~ is_true (const_list ?es) /\ _ =>
      let Hs := fresh "Hs" in
      assert (Hs : ~ is_true (const_list es) /\ ~ trapping es)
        by (eapply nc_shape; [ hd_solve | discriminate | intros; discriminate ]);
      destruct Hs as [Hs1 Hs2];
      split; [ exact Hs1 | intros Ht; exfalso; exact (Hs2 Ht) ]
  end.

Lemma not_const_label_singleton : forall n a b,
  ~ is_true (const_list [AI_label n a b]).
Proof.
  intros n a b H. apply (not_const_label n a b). exact (const_cons_head _ _ H).
Qed.

Lemma reduce_simple_nc_trapping : forall es es',
  reduce_simple es es' ->
  ~ is_true (const_list es) /\ (trapping es -> trapping es').
Proof.
  intros es es' Hred. induction Hred.
  all: try (solve [ nc_auto ]).
  (* the four rules whose redex may legitimately be a label or a trap *)
  { (* rs_label_const: a trapped body is not a value list, so this rule
       cannot have fired on a trapping configuration -- but the successor
       is the body anyway, so the implication holds outright *)
    split; [ apply not_const_label_singleton |].
    intros Ht. exact (trapping_label_inv _ _ _ Ht). }
  { (* rs_label_trap *)
    split; [ apply not_const_label_singleton |].
    intros _. exact trapping_trap. }
  { (* rs_br: a trapped body has no pending branch, so this is vacuous *)
    split; [ apply not_const_label_singleton |].
    intros Ht. exfalso. apply trapping_label_inv in Ht.
    match goal with
    | H : lfill ?lhx _ = ?LI |- _ => rewrite <- H in Ht
    end.
    eapply trapping_no_br; [ eassumption | exact Ht ]. }
  { (* rs_trap: the redex is trapping by construction *)
    split.
    - intros Hc. apply (trapping_not_const es); [| exact Hc ].
      match goal with
      | H : lfill ?lhx [AI_trap] = es |- _ => exists _, lhx; symmetry; exact H
      end.
    - intros _. exact trapping_trap. }
Qed.


Lemma reduce_nc_trapping : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  ~ is_true (const_list es) /\ (trapping es -> trapping es').
Proof.
  intros hs s f es hs' s' f' es' Hred. induction Hred.
  all: try (solve [ nc_auto ]).
  all: try (solve [ eapply reduce_simple_nc_trapping; eassumption ]).
  (* the invocations state their argument list as a v_to_e_list *)
  all: try (solve [ match goal with
                    | H : _ = v_to_e_list _ |- _ => rewrite H
                    end; nc_auto ]).
  { (* r_label: the hole carries both facts up through the context *)
    destruct IHHred as [Hnc Htp]. subst les. subst les'. split.
    - intros Hc. exact (Hnc (lfill_const_inv _ _ _ Hc)).
    - intros Ht. destruct (trapping_lfill_inv _ _ _ Ht) as [Hc | Htes].
      + exfalso. exact (Hnc Hc).
      + apply trapping_lfill. exact (Htp Htes). }
Qed.

(* A body that has already trapped stays trapped when its hole steps. *)
Lemma reduce_trapping : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  forall k (lh : lholed k), trapping (lfill lh es) -> trapping (lfill lh es').
Proof.
  intros hs s f es hs' s' f' es' Hred k lh Ht.
  destruct (reduce_nc_trapping _ _ _ _ _ _ _ _ Hred) as [Hnc Htp].
  destruct (trapping_lfill_inv _ _ _ Ht) as [Hc | Htes].
  - exfalso. exact (Hnc Hc).
  - apply trapping_lfill. exact (Htp Htes).
Qed.

Lemma lh_labels_ok_step : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  forall k (lh : lholed k) K, lh_labels_ok lh es K -> lh_labels_ok lh es' K.
Proof.
  intros hs s f es hs' s' f' es' Hred k lh K Hok.
  eapply lh_labels_ok_step_gen;
  [ exact Hok
  | eapply reduce_nobr; exact Hred
  | eapply reduce_hazard_or_trap; exact Hred
  | intros kk lhx Ht; eapply reduce_trapping; [ exact Hred | exact Ht ] ].
Qed.

(* ══════════════════════════════════════════════════════════════════
   The frame-free steps.
   ══════════════════════════════════════════════════════════════════
   reduce_simple never touches the locals, so the frame plays no part
   here and only the live-set containment has to come back out. *)

Ltac sim_simple_plain :=
  match goal with
  | Hrel : rel_es _ _ _ ?eo |- _ =>
      apply rel_es_plain_inv in Hrel; [ subst eo | solve [plain_solve] ]
  end;
  eexists; split; [| split];
  [ econstructor; first [ eassumption | reflexivity ]
  | apply rel_es_plain; solve [plain_solve]
  | live_sub_solve ].

Lemma sim_simple : forall es es',
  reduce_simple es es' ->
  forall phi K es_o,
    rel_es phi K es es_o ->
    exists es_o',
      reduce_simple es_o es_o' /\
      rel_es phi K es' es_o' /\
      (forall i, live_ext es' K i -> live_ext es K i).
Proof.
  intros es es' Hrs. induction Hrs; intros phi K es_o Hrel.
  all: try (solve [ sim_simple_plain ]).
  { (* rs_label_const: the body has finished, the label is popped *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_label_inv in He.
    destruct He as [a_o [b_o [Hlo [Hlab [Ha Hb]]]]]. subst e_o.
    apply rel_es_plain_inv in Hb; [| apply es_plain_const_list; assumption ].
    subst b_o.
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
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_label_inv in He.
    destruct He as [a_o [b_o [Hlo [Hlab [Ha Hb]]]]]. subst e_o.
    apply rel_es_plain_inv in Hb; [| solve [plain_solve] ]. subst b_o.
    eexists. split; [| split].
    - apply rs_label_trap.
    - apply rel_es_plain. solve [plain_solve].
    - intros ix Hl. destruct (live_ext_trap K ix Hl).
  }
  { (* rs_if_false *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply (rel_e_v_inv _ _ (VAL_num (VAL_int32 c))) in He. subst e_o.
    apply rel_es_cons_inv in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
    apply rel_es_nil_inv in Ht1. subst t1. subst t_o. subst es_o.
    apply rel_e_basic_inv in He1. destruct He1 as [b_o [Hb1 Hb]]. subst e1.
    apply rel_b_if_inv in Hb.
    destruct Hb as [b1_o [b2_o [Hbo [Hw1 [Hw2 [Hr1 Hr2]]]]]].
    subst b_o.
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
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply (rel_e_v_inv _ _ (VAL_num (VAL_int32 c))) in He. subst e_o.
    apply rel_es_cons_inv in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
    apply rel_es_nil_inv in Ht1. subst t1. subst t_o. subst es_o.
    apply rel_e_basic_inv in He1. destruct He1 as [b_o [Hb1 Hb]]. subst e1.
    apply rel_b_if_inv in Hb.
    destruct Hb as [b1_o [b2_o [Hbo [Hw1 [Hw2 [Hr1 Hr2]]]]]].
    subst b_o.
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
  { (* rs_br: the body branches out to the label's continuation *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_label_inv in He.
    destruct He as [a_o [b_o [Hlo [Hlab [Ha Hb]]]]]. subst e_o.
    subst LI. apply rel_es_lfill_inv in Hb.
    destruct Hb as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv in Hhole; [| solve [plain_solve] ]. subst hole_o.
    subst b_o.
    eexists. split; [| split].
    - eapply rs_br; [ eassumption | eassumption | reflexivity ].
    - apply rel_es_app.
      + apply rel_es_plain. apply es_plain_const_list. assumption.
      + eapply rel_es_weaken; [ exact Ha |].
        intros ix Hx. apply live_ext_nil. exact Hx.
    - (* What the continuation a reads after the branch must already have
         counted as live at the label.  The label's liveness gates a behind
         the body's kills, so this needs es_kills_b ix LI = false: a kill
         inside the body must not shadow the continuation, because the br
         jumps over it.  That is exactly what label_ok grants: the body has
         no branch at all (so this rule never fires), or it kills nothing
         that matters, or the label's live-out is empty, or it has already
         trapped -- and a trapped body has no pending br either. *)
      intros ix Hl.
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
  { (* rs_local_const: the activation has finished *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    apply rel_es_plain_inv in Hes; [| apply es_plain_const_list; assumption ].
    subst esf_o.
    eexists. split; [| split].
    - eapply rs_local_const; eassumption.
    - apply rel_es_plain. apply es_plain_const_list. assumption.
    - intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl).
      apply es_neutral_const_list; assumption.
  }
  { (* rs_local_trap *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    apply rel_es_plain_inv in Hes; [| solve [plain_solve] ]. subst esf_o.
    eexists. split; [| split].
    - apply rs_local_trap.
    - apply rel_es_plain. solve [plain_solve].
    - intros ix Hl. destruct (live_ext_trap K ix Hl).
  }
  { (* rs_local_tee: the one simple rule that mentions a local.  Its
       obligation is discharged by the tee's own slot_free, which is the
       set's obligation at the same context. *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_e_v_inv in He. subst e_o.
    apply rel_es_cons_inv in Ht. destruct Ht as [e1 [t1 [Heq1 [He1 Ht1]]]].
    apply rel_es_nil_inv in Ht1. subst t1. subst t_o. subst es_o.
    apply rel_e_basic_inv in He1. destruct He1 as [b_o [Hb1 Hb]]. subst e1.
    apply rel_b_tee_inv in Hb. destruct Hb as [Hbo Hsf]. subst b_o.
    eexists. split; [| split].
    - apply rs_local_tee.
    - apply rel_cons; [ apply rel_e_v_to_e |].
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
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    subst es. apply rel_es_lfill_inv in Hes.
    destruct Hes as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv in Hhole; [| solve [plain_solve] ]. subst hole_o.
    subst esf_o.
    eexists. split; [| split].
    - eapply rs_return; [ eassumption | eassumption | reflexivity ].
    - apply rel_es_plain. apply es_plain_const_list. assumption.
    - intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl).
      apply es_neutral_const_list; assumption.
  }
  { (* rs_trap: the context around the trap is discarded.  Nothing is live
       after a trap, so the containment is vacuous. *)
    subst es. apply rel_es_lfill_inv in Hrel.
    destruct Hrel as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv in Hhole; [| solve [plain_solve] ]. subst hole_o.
    subst es_o.
    eexists. split; [| split].
    - eapply rs_trap; [| reflexivity ].
      intros Habs. apply H. eapply rel_lh_trap_inv; eassumption.
    - apply rel_es_plain. solve [plain_solve].
    - intros ix Hl. destruct (live_ext_trap K ix Hl).
  }
Qed.

(* ── How rs_br is closed ──────────────────────────────────────────
   All 37 reduce_simple rules are closed above.  rs_br was the hard one,
   and it is worth recording why, because the shape of label_ok is
   entirely determined by it.

   ai_live/ai_kills gate a label's branch continuation a behind the body's
   kills:

     ai_live  (AI_label n a b) = live b || (~kills b && live a)
     ai_kills (AI_label n a b) = kills b

   That gate is what makes live_ext (lfill lh X) K *equal* to
   live_ext X (lh_K lh K) -- live_ext_lfill -- which is what r_label needs
   in order to pass the frame agreement down to the hole and take the
   successor's back up.  Weakening the gate (counting a's reads ungated)
   would restore rs_br but break that equality, and with it r_label.  So
   the gate stays and rs_br must instead be given, as a side condition,
   the fact that the body kills nothing that shadows a.  There are exactly
   two sources of kills, and label_ok's three disjuncts answer them:

     - local.set / local.tee.  Excluded inside a label body: the pass
       rejects those at nesting depth > 0 (bi_guarded), and relb_block /
       relb_if / relb_loop carry bs_writes = false.  The one label whose
       body may write is the one wrapping a whole function body, whose
       branch continuation is empty and whose live-out K is empty (it sits
       directly under a frame) -- hence label_ok's second alternative,
       "a reads nothing and K is empty", which is why K is threaded
       through label_ok at all.

       The first alternative asks for hazard-freedom rather than the
       kill-freedom it really needs, because kill-freedom is not preserved
       by a step: bi_kills treats a block as killing nothing (a branch may
       skip it), so [block bt [local.set 0]] kills nothing while its
       r_block successor [AI_label 0 [] [local.set 0]] does.  es_hazard
       counts writes wherever they are nested, which both implies
       kill-freedom (es_hazard_kills) and survives a step.

     - AI_trap, which kills because nothing runs after a trap (rs_trap
       needs exactly that).  A body vs ++ [br j] ++ [AI_trap] reports a
       kill it never performs.  No source program has that shape and no
       reachable state does either -- lfill's prefix must be values, so no
       step can produce a trap to the right of a br.  Rather than carry a
       syntactic well-formedness invariant, label_ok admits the escape
       hatch `trapping b`: once the body has trapped it is lfill lh
       [AI_trap], and trapping_no_br says such a list has no pending br,
       so the rs_br case is simply vacuous there.  trapping is preserved
       by reduction (reduce_trapping, via reduce_nc_trapping) and every
       step either preserves hazard-freedom or lands in trapping
       (reduce_hazard_or_trap), which is what lh_labels_ok_step needs to
       push label_ok across a step. *)

(* ══════════════════════════════════════════════════════════════════
   The forward simulation, one step.
   ══════════════════════════════════════════════════════════════════ *)

Theorem sim_step : forall hs s f es hs' s' f' es',
  reduce hs s f es hs' s' f' es' ->
  store_guarded s ->
  forall phi K f_o es_o,
    rel_es phi K es es_o ->
    frames_agree phi (live_ext es K) f f_o ->
    exists f_o' es_o',
      reduce hs s f_o es_o hs' s' f_o' es_o' /\
      rel_es phi K es' es_o' /\
      frames_agree phi (live_ext es' K) f' f_o'.
Proof.
  intros hs s f es hs' s' f' es' Hred Hstore.
  induction Hred; intros phi K f_o es_o Hrel Hfr.
  all: try (solve [ sim_plain ]).
  all: try (solve [ eapply sim_local_get; eassumption ]).
  all: try (solve [ eapply sim_local_set;
                    [ eassumption | apply leq_to_lt; eassumption
                    | eassumption | eassumption | eassumption ] ]).
  (* the host calls are plain too, once their argument list is unfolded *)
  all: try (solve [ subst ves; sim_plain ]).
  { (* r_simple *)
    destruct (sim_simple _ _ H phi K es_o Hrel) as [es_o' [Hrs [Hrel' Hsub]]].
    exists f_o, es_o'. split; [| split].
    - apply r_simple. exact Hrs.
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
    eexists. eexists. split; [| split].
    - eapply r_block; [ rewrite <- Hinst; eassumption | eassumption
                      | eassumption | eassumption | eassumption ].
    - apply rel_cons; [| apply rel_nil ].
      apply rel_label.
      + (* whichever way the block body is guarded, the label inherits it:
           branch-free bodies stay branch-free once moved under the label,
           and write-free ones carry no hazard either, since the values in
           front of them and a fresh body carry no trap *)
        destruct Hbw as [Hbr | Hbw].
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
    eexists. eexists. split; [| split].
    - eapply r_loop; [ rewrite <- Hinst; eassumption | eassumption
                     | eassumption | eassumption | eassumption ].
    - apply rel_cons; [| apply rel_nil ].
      apply rel_label.
      + (* a loop body that branches back re-runs, so it must not write;
           a branch-free one runs once and is a block in disguise *)
        destruct Hnw as [Hbr | Hnw'].
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
  { (* r_return_call *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    eexists. eexists. split; [| split].
    - apply r_return_call. eapply reduce_call_transport;
        [ eassumption | symmetry; exact Hinst ].
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call_indirect_success *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    eexists. eexists. split; [| split].
    - apply r_return_call_indirect_success.
      eapply reduce_call_indirect_success_transport;
        [ eassumption | symmetry; exact Hinst ].
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_return_call_indirect_failure *)
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    eexists. eexists. split; [| split].
    - apply r_return_call_indirect_failure.
      eapply reduce_call_indirect_failure_transport;
        [ eassumption | symmetry; exact Hinst ].
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr); live_sub_solve.
  }
  { (* r_invoke_native: a fresh activation, related to itself under the
       identity map -- the callee is optimized separately. *)
    subst ves.
    apply rel_es_plain_inv in Hrel; [| solve [plain_solve] ]. subst es_o.
    pose proof (proj1 Hfr) as Hinst.
    assert (Hlf : bs_guarded (modfunc_body code) = true)
      by (eapply Hstore; subst cl; eassumption).
    eexists. eexists. split; [| split].
    - eapply r_invoke_native; try eassumption; try reflexivity.
    - apply rel_cons; [| apply rel_nil ].
      eapply rel_frame; [ apply frames_agree_empty_refl |].
      apply rel_cons; [| apply rel_nil ].
      apply rel_label; [| apply rel_nil |].
      * (* the one label whose body may write: its branch continuation is
           empty and its live-out is empty, since it sits under a frame *)
        apply label_ok_dead; [ reflexivity |].
        intros i Hi. rewrite ! live_ext_nil in Hi. exact Hi.
      * apply rel_es_to_e_list. apply rel_bs_refl.
        subst code. exact Hlf.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl. rewrite live_ext_frame in Hl.
      apply live_ext_neutral_bwd; [ solve [neutral_solve] | exact Hl ].
  }
  { (* r_return_invoke: a return from inside an activation *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    subst es. apply rel_es_lfill_inv in Hes.
    destruct Hes as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]].
    apply rel_es_plain_inv in Hhole; [| solve [plain_solve] ]. subst hole_o.
    subst esf_o.
    eexists. eexists. split; [| split].
    - eapply r_return_invoke; try eassumption; try reflexivity.
    - apply rel_es_plain. solve [plain_solve].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros ix Hl. apply live_ext_frame.
      refine (live_ext_neutral_fwd _ _ ix _ Hl); solve [neutral_solve].
  }
  { (* r_label: step inside a context.  The live set of a filled context is
       exactly the hole's, so the invariant goes down and comes back. *)
    subst les les'.
    apply rel_es_lfill_inv in Hrel.
    destruct Hrel as [lh_o [hole_o [Hheq [Hlh [Hok Hhole]]]]]. subst es_o.
    destruct (IHHred Hstore phi (lh_K lh K) f_o hole_o Hhole
                (frames_agree_sub _ _ _ _ _
                   (fun i Hi => proj2 (live_ext_lfill _ lh es K i) Hi) Hfr))
      as [f_o' [hole_o' [Hr [Hrel' Hfr']]]].
    exists f_o', (lfill lh_o hole_o'). split; [| split].
    - eapply r_label; [ exact Hr | reflexivity | reflexivity ].
    - apply rel_es_lfill; [ exact Hlh | | exact Hrel' ].
      eapply lh_labels_ok_step; [ exact Hred | exact Hok ].
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr').
      intros i Hi. apply live_ext_lfill. exact Hi.
  }
  { (* r_frame: step inside an activation, under its own map *)
    apply rel_es_cons_inv in Hrel. destruct Hrel as [e_o [t_o [Heq [He Ht]]]].
    apply rel_es_nil_inv in Ht. subst t_o. subst es_o.
    apply rel_e_frame_inv in He.
    destruct He as [fr_o [esf_o [psi [Hfo [Hfa Hes]]]]]. subst e_o.
    assert (Hin : frames_agree psi (live_ext es (fun _ => False)) f fr_o).
    { refine (frames_agree_sub _ _ _ _ _ _ Hfa).
      intros ix Hi. unfold live_ext, es_live in *.
      destruct Hi as [H' | [_ Hf]]; [ exact H' | destruct Hf ]. }
    destruct (IHHred Hstore psi (fun _ => False) fr_o esf_o Hes Hin)
      as [fr_o' [esf_o' [Hr [Hrel' Hfa']]]].
    eexists. eexists. split; [| split].
    - apply r_frame. exact Hr.
    - apply rel_cons; [| apply rel_nil ].
      eapply rel_frame; [| exact Hrel' ].
      refine (frames_agree_sub _ _ _ _ _ _ Hfa').
      intros i Hi. left. exact Hi.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hl. apply live_ext_frame. apply live_ext_frame in Hl. exact Hl.
  }
Qed.

(* ── r_block / r_loop helpers ───────────────────────────────────── *)

Lemma map_eq_nil_l : forall A B (f : A -> B) l, List.map f l = [] -> l = [].
Proof. intros. destruct l; [reflexivity | discriminate H]. Qed.

Lemma map_apply_phi_id : forall phi l,
  (forall b, In b l -> apply_phi phi b = b) ->
  List.map (apply_phi phi) l = l.
Proof.
  induction l as [|x r IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H x (or_introl eq_refl)).
    rewrite (IH (fun b Hb => H b (or_intror Hb))). reflexivity.
Qed.

Lemma const_list_in : forall l e, is_true (const_list l) -> In e l -> is_const e = true.
Proof.
  intros l e H Hin.
  apply (proj1 (forallb_forall is_const l) H). exact Hin.
Qed.

(* The direct whole-body single-step attempt that used to live here has been
   removed.  It could not be closed: its induction hypothesis relates only
   whole bodies, so the r_label constructor -- which proves lfill lh es ->
   lfill lh es' from an inner step on the *fragment* es -- had no usable
   IH.  Its statement is now proved admit-free below as
   coalesce_func_correct_body, a three-line corollary of the pointwise
   theorem coalesce_func_correct_ctx. *)

(* Renamed from coalesce_module_correct, which it never was: the real
   whole-module result is the theorem of that name in
   toplevel_correct.v, and two constants cannot share it. *)
Theorem apply_phi_module_funcs : forall phi m,
  let m' := apply_phi_module phi m in
  forall f, In f m.(mod_funcs) ->
            In (apply_phi_func phi f) m'.(mod_funcs).
Proof.
  intros. subst m'. simpl. apply in_map. exact H.
Qed.

(* ══════════════════════════════════════════════════════════════════
   The pointwise (contextual) simulation.
   ══════════════════════════════════════════════════════════════════

   A whole-body statement -- one relating only
   List.map AI_basic (modfunc_body f) to its coalesced counterpart --
   cannot be proved, because its induction hypothesis is usable only on
   whole bodies.  The r_label constructor reduces under a filled label
   context (lfill lh es), so the inner step's list es is a proper
   fragment of the body and the IH can never fire.  (The shape defence
   that dismisses r_frame -- an all-AI_basic list contains no frames --
   does not transfer, because an all-basic list certainly can be a
   filled label context.)

   The fix is to relate code lists *pointwise* under apply_phi_es, a lift
   of apply_phi to administrative instructions.  That relation applies to
   arbitrary fragments and is closed under label filling, so the induction
   goes through -- r_label included -- and the whole-body and multi-step
   statements both drop out as corollaries at the end of this section. *)

(* apply_phi lifted to the administrative-instruction level.  It recurses
   into label bodies (same function activation, code the pass renamed) but
   stops at frames (a different activation, whose body came from the store
   untouched); see the AI_frame branch. *)
Fixpoint apply_phi_es (phi : local_map) (e : administrative_instruction) : administrative_instruction :=
  match e with
  | AI_basic b            => AI_basic (apply_phi phi b)
  | AI_trap               => AI_trap
  | AI_ref a              => AI_ref a
  | AI_ref_extern eaddr   => AI_ref_extern eaddr
  | AI_invoke a           => AI_invoke a
  | AI_return_invoke a    => AI_return_invoke a
  | AI_label n es es'     => AI_label n (List.map (apply_phi_es phi) es)
                                          (List.map (apply_phi_es phi) es')
  (* phi is a *function-local* rename, so the lift must stop at frame
     boundaries: AI_frame marks a different function's activation, whose body
     came from the store and was never touched by this phi.  Recursing here
     would demand that the callee's code also be renamed, which no reduce step
     ever establishes (see r_invoke_native), and is what previously made the
     invoke family unprovable. *)
  | AI_frame n f es       => AI_frame n f es
  end.

(* Values and their lifted instruction forms are apply_phi-stable. *)
Lemma apply_phi_es_v_to_e : forall phi v,
  apply_phi_es phi (v_to_e v) = v_to_e v.
Proof.
  intros phi v. destruct v; simpl; try reflexivity.
  destruct v; simpl; reflexivity.
Qed.

Lemma map_apply_phi_es_v_to_e_list : forall phi vs,
  List.map (apply_phi_es phi) (v_to_e_list vs) = v_to_e_list vs.
Proof.
  intros phi vs. unfold v_to_e_list. rewrite List.map_map.
  apply List.map_ext. exact (apply_phi_es_v_to_e phi).
Qed.

(* apply_phi_es lifted to label holes: recurse into the surrounding
   instruction lists and the inner hole; values stay untouched. *)
Fixpoint apply_phi_es_lh {k} (phi : local_map) (lh : lholed k) : lholed k :=
  match lh with
  | LH_base vs es        => LH_base vs (List.map (apply_phi_es phi) es)
  | LH_rec _ vs n es lh' es'' =>
      LH_rec vs n (List.map (apply_phi_es phi) es)
                  (apply_phi_es_lh phi lh')
                  (List.map (apply_phi_es phi) es'')
  end.

(* apply_phi_es is a homomorphism for label filling. *)
Lemma apply_phi_es_lfill : forall phi k (lh : lholed k) es,
  List.map (apply_phi_es phi) (lfill lh es) =
  lfill (apply_phi_es_lh phi lh) (List.map (apply_phi_es phi) es).
Proof.
  intros phi k lh. induction lh; intros es; simpl.
  - rewrite List.map_app. rewrite List.map_app.
    rewrite map_apply_phi_es_v_to_e_list. reflexivity.
  - rewrite List.map_app.
    rewrite map_apply_phi_es_v_to_e_list.
    cbn.
    rewrite IHlh.
    reflexivity.
Qed.

(* Pointwise list-relation helpers used across every ctx reduce case. *)
Lemma map_cons_inv : forall A B (f : A -> B) l a t,
  List.map f l = a :: t ->
  exists a' t', l = a' :: t' /\ f a' = a /\ List.map f t' = t.
Proof.
  intros A B f l a t H.
  destruct l; [discriminate H |].
  exists a0, l. injection H as H1 H2. exact (conj eq_refl (conj H1 H2)).
Qed.

Lemma apply_phi_es_basic_inv : forall phi e b,
  apply_phi_es phi e = AI_basic b ->
  exists b', e = AI_basic b' /\ apply_phi phi b' = b.
Proof.
  intros phi e b H. destruct e; simpl in H; try (discriminate H).
  injection H as Hb. exists b0. exact (conj eq_refl Hb).
Qed.

Lemma apply_phi_es_basic_inv_eq : forall phi e b,
  apply_phi_es phi e = AI_basic b ->
  is_complex_basic b = false ->
  e = AI_basic b.
Proof.
  intros phi e b H Hc.
  destruct (apply_phi_es_basic_inv phi e b H) as [b' [He Hb']].
  subst e.
  assert (Hbb : b' = b).
  { eapply apply_phi_preserves; [exact Hb' | exact Hc]. }
  rewrite Hbb. reflexivity.
Qed.

(* The body of a block/loop/if is a list of basic instructions, so
   apply_phi_es on AI_basic (BI_block ...) only renames locals inside. *)
Lemma apply_phi_es_block_inv : forall phi e tb es,
  apply_phi_es phi e = AI_basic (BI_block tb es) ->
  exists es', e = AI_basic (BI_block tb es') /\
    List.map (apply_phi phi) es' = es.
Proof.
  intros phi e tb es H.
  destruct e; simpl in H; try (discriminate H).
  injection H as Hb.
  destruct b; simpl in Hb; try discriminate Hb.
  injection Hb as Htb Hes.
  exists l. rewrite Htb. split; [reflexivity | exact Hes].
Qed.

Lemma apply_phi_es_loop_inv : forall phi e tb es,
  apply_phi_es phi e = AI_basic (BI_loop tb es) ->
  exists es', e = AI_basic (BI_loop tb es') /\
    List.map (apply_phi phi) es' = es.
Proof.
  intros phi e tb es H.
  destruct e; simpl in H; try (discriminate H).
  injection H as Hb.
  destruct b; simpl in Hb; try discriminate Hb.
  injection Hb as Htb Hes.
  exists l. rewrite Htb. split; [reflexivity | exact Hes].
Qed.

Lemma apply_phi_es_if_inv : forall phi e tb es1 es2,
  apply_phi_es phi e = AI_basic (BI_if tb es1 es2) ->
  exists es1' es2', e = AI_basic (BI_if tb es1' es2') /\
    List.map (apply_phi phi) es1' = es1 /\
    List.map (apply_phi phi) es2' = es2.
Proof.
  intros phi e tb es1 es2 H.
  destruct e; simpl in H; try (discriminate H).
  injection H as Hb.
  destruct b; simpl in Hb; try discriminate Hb.
  injection Hb as Htb Hes1 Hes2.
  exists l, l0. rewrite Htb. split; [reflexivity |].
  exact (conj Hes1 Hes2).
Qed.

(* A basic instruction whose apply_phi image is a local op is the local op. *)
Lemma apply_phi_es_local_get_inv : forall phi e i,
  apply_phi_es phi e = AI_basic (BI_local_get i) ->
  exists i', e = AI_basic (BI_local_get i') /\ apply_phi_local phi i' = i.
Proof.
  intros phi e i H.
  destruct e; simpl in H; try (discriminate H).
  injection H as Hb.
  destruct b; simpl in Hb; try discriminate Hb.
  injection Hb as Hi.
  exists l. exact (conj eq_refl Hi).
Qed.

Lemma apply_phi_es_local_set_inv : forall phi e i,
  apply_phi_es phi e = AI_basic (BI_local_set i) ->
  exists i', e = AI_basic (BI_local_set i') /\ apply_phi_local phi i' = i.
Proof.
  intros phi e i H.
  destruct e; simpl in H; try (discriminate H).
  injection H as Hb.
  destruct b; simpl in Hb; try discriminate Hb.
  injection Hb as Hi.
  exists l. exact (conj eq_refl Hi).
Qed.

(* The inverse direction: if a pointwise apply_phi-image of es_src has a
   label-filled shape, then es_src itself is that shape, with its inner
   fragment the corresponding preimage.  This is what makes the r_label
   step in coalesce_func_correct_ctx go through: the source side steps on
   the inner fragment and re-fills the (apply_phi-lifted) label hole. *)

(* A map-image split into three parts comes from splitting the source. *)
Lemma firstn_length_app : forall A (l m : list A),
  List.firstn (length l) (l ++ m) = l.
Proof.
  intros A l m. induction l; simpl; [reflexivity | rewrite IHl; reflexivity].
Qed.

Lemma skipn_length_app : forall A (l m : list A),
  List.skipn (length l) (l ++ m) = m.
Proof.
  intros A l m. induction l; simpl; [reflexivity | rewrite IHl; reflexivity].
Qed.

Lemma map_app_split3 : forall A B (f : A -> B) l (a m c : list B),
  List.map f l = a ++ m ++ c ->
  exists l1 l2 l3,
    l = l1 ++ l2 ++ l3 /\
    List.map f l1 = a /\ List.map f l2 = m /\ List.map f l3 = c.
Proof.
  intros A B f l a m c H.
  exists (List.firstn (length a) l).
  exists (List.firstn (length m) (List.skipn (length a) l)).
  exists (List.skipn (length m) (List.skipn (length a) l)).
  assert (Hsplit : l = List.firstn (length a) l ++
                        (List.firstn (length m) (List.skipn (length a) l) ++
                         List.skipn (length m) (List.skipn (length a) l))).
  { rewrite (List.firstn_skipn (length m) (List.skipn (length a) l)).
    rewrite (List.firstn_skipn (length a) l).
    reflexivity. }
  assert (Hm1 : List.map f (List.firstn (length a) l) = a).
  { rewrite <- (List.firstn_map f (length a) l). rewrite H.
    change (List.firstn (length a) (a ++ (m ++ c)) = a).
    apply firstn_length_app. }
  assert (Hm2 : List.map f (List.firstn (length m) (List.skipn (length a) l)) = m).
  { rewrite <- (List.firstn_map f (length m) (List.skipn (length a) l)).
    rewrite <- (List.skipn_map f (length a) l). rewrite H.
    rewrite (@skipn_length_app B a (m ++ c)).
    apply firstn_length_app. }
  assert (Hm3 : List.map f (List.skipn (length m) (List.skipn (length a) l)) = c).
  { rewrite <- (List.skipn_map f (length m) (List.skipn (length a) l)).
    rewrite <- (List.skipn_map f (length a) l). rewrite H.
    rewrite (@skipn_length_app B a (m ++ c)).
    rewrite skipn_length_app. reflexivity. }
  split; [exact Hsplit |].
  split; [exact Hm1 |].
  split; [exact Hm2 | exact Hm3].
Qed.

(* An element whose apply_phi_es image is a rank-5 value instruction is that
   instruction. *)
Lemma apply_phi_es_v_to_e_inv : forall phi e (v : value),
  apply_phi_es phi e = v_to_e v ->
  e = v_to_e v.
Proof.
  intros phi e v Hv.
  destruct v as [vn | vv | vref]; simpl in Hv.
  - destruct e as [b | | | | | | |]; simpl in Hv; try (inversion Hv).
    injection Hv as H1.
    assert (Hb : b = BI_const_num vn).
    { eapply apply_phi_preserves; [exact H1 | reflexivity]. }
    rewrite Hb. reflexivity.
  - destruct e as [b | | | | | | |]; simpl in Hv; try (inversion Hv).
    injection Hv as H1.
    assert (Hb : b = BI_const_vec vv).
    { eapply apply_phi_preserves; [exact H1 | reflexivity]. }
    rewrite Hb. reflexivity.
  - destruct vref as [rt | fa | ea]; simpl in Hv.
    + destruct e as [b | | | | | | |]; simpl in Hv; try (inversion Hv).
      injection Hv as H1.
      assert (Hb : b = BI_ref_null rt).
      { eapply apply_phi_preserves; [exact H1 | reflexivity]. }
      rewrite Hb. reflexivity.
    + destruct e as [b | | | | | | |]; simpl in Hv; try (inversion Hv).
      reflexivity.
    + destruct e as [b | | | | | | |]; simpl in Hv; try (inversion Hv).
      reflexivity.
Qed.

Lemma map_apply_phi_es_v_to_e_list_inv : forall phi l vs,
  List.map (apply_phi_es phi) l = v_to_e_list vs ->
  l = v_to_e_list vs.
Proof.
  intros phi l vs H. unfold v_to_e_list in H.
  induction vs in l, H |- *.
  - simpl in H. destruct l; [reflexivity | discriminate H].
  - simpl in H.
    destruct l; [discriminate H |].
    simpl in H. injection H as He Hrest.
    assert (Hf : a0 = v_to_e a).
    { exact (apply_phi_es_v_to_e_inv phi a0 a He). }
    rewrite Hf.
    simpl. f_equal. exact (IHvs l Hrest).
Qed.

(* apply_phi_es on a non-basic constructor is that constructor, with its
   nested lists mapped.  Enough inversion for the singleton cases below. *)
Lemma apply_phi_es_label_inv : forall phi e n b c,
  apply_phi_es phi e = AI_label n b c ->
  exists b' c', e = AI_label n b' c' /\
    List.map (apply_phi_es phi) b' = b /\
    List.map (apply_phi_es phi) c' = c.
Proof.
  intros phi e n b c H. destruct e; simpl in H; try discriminate H.
  injection H as Hn Hb Hc.
  subst n0.
  exists l, l0. split; [reflexivity |].
  exact (conj Hb Hc).
Qed.

Lemma map_singleton_inv : forall A B (f : A -> B) l x,
  List.map f l = [x] ->
  exists y, l = [y] /\ f y = x.
Proof.
  intros A B f l x H.
  destruct l; [discriminate H |].
  destruct l; [| discriminate H].
  simpl in H. injection H as Hf.
  exists a. split; [reflexivity | exact Hf].
Qed.

Lemma lfill_preimage :
  forall phi k (lh : lholed k) es_src es_opt,
    List.map (apply_phi_es phi) es_src = lfill lh es_opt ->
    exists (lh_src : lholed k) es_src_inner,
      apply_phi_es_lh phi lh_src = lh /\
      es_src = lfill lh_src es_src_inner /\
      List.map (apply_phi_es phi) es_src_inner = es_opt.
Proof.
  intros phi k lh.
  induction lh; intros es_src es_opt H.
  - (* LH_base l l0 : v_to_e_list l ++ es_opt ++ l0 *)
    simpl in H.
    destruct (map_app_split3 _ _ (apply_phi_es phi) es_src (v_to_e_list l) es_opt l0 H) as
      [l1 [l2 [l3 [Hl [Hl1 [Hl2 Hl3]]]]]].
    assert (Hl1e : l1 = v_to_e_list l).
    { exact (map_apply_phi_es_v_to_e_list_inv phi l1 l Hl1). }
    exists (LH_base l l3), l2.
    split.
    { simpl. rewrite Hl3. reflexivity. }
    split.
    { rewrite Hl. rewrite Hl1e. reflexivity. }
    { exact Hl2. }
  - (* LH_rec k l n l0 lh l1 : v_to_e_list l ++ [AI_label n l0 (lfill lh es_opt)] ++ l1 *)
    simpl in H.
    destruct (map_app_split3 _ _ (apply_phi_es phi) es_src (v_to_e_list l)
               [AI_label n l0 (lfill lh es_opt)] l1 H) as
      [l2 [l3 [l4 [Hl [Hl1 [Hl2 Hl3]]]]]].
    assert (Hl1e : l2 = v_to_e_list l).
    { exact (map_apply_phi_es_v_to_e_list_inv phi l2 l Hl1). }
    (* l3 maps to the singleton [AI_label n l0 (lfill lh es_opt)] *)
    assert (Hl3e : exists e, l3 = [e] /\ apply_phi_es phi e = AI_label n l0 (lfill lh es_opt)).
    { exact (map_singleton_inv _ _ (apply_phi_es phi) l3 (AI_label n l0 (lfill lh es_opt)) Hl2). }
    destruct Hl3e as [e [Hl3s Hl3map]].
    destruct (apply_phi_es_label_inv phi e n l0 (lfill lh es_opt) Hl3map) as
      [b' [c' [He [Hbm Hcm]]]].
    (* c' is the inner body of the label: map apply_phi_es c' = lfill lh es_opt *)
    destruct (IHlh c' es_opt Hcm) as [lh_src' [es_src_inner [Hlh' [Hc' Hinner]]]].
    exists (LH_rec l n b' lh_src' l4), es_src_inner.
    split.
    { simpl. rewrite Hbm. rewrite Hlh'. rewrite Hl3. reflexivity. }
    split.
    { rewrite Hl. rewrite Hl1e. rewrite Hl3s. subst e.
      simpl. rewrite Hc'. reflexivity. }
    { exact Hinner. }
Qed.

(* ── Pointwise single-step simulation (the strengthened IH) ───────── *)

(* The whole-body statement generalised to "any code list, related
   pointwise to its source counterpart".  When es_opt is a label-filled
   fragment (lfill lh es), the premise still holds, so the r_label
   constructor becomes provable by induction on the reduce derivation. *)
(* ── reduce_simple simulation under the pointwise map ────────────── *)
(* On inputs that contain no AI_label / AI_frame and whose AI_basic parts
   are all non-complex, the pointwise map is the identity, so the source
   list equals the target list and reduce_simple replays identically. *)

(* AI_frame is now fixed: apply_phi_es leaves frames verbatim. *)
Definition apes_fixed (x : administrative_instruction) : Prop :=
  match x with
  | AI_label _ _ _ => False
  | AI_basic b => is_complex_basic b = false
  | _ => True
  end.

Lemma apply_phi_es_fixed : forall phi x,
  apes_fixed x -> apply_phi_es phi x = x.
Proof.
  intros phi x Hx. destruct x; simpl in *; try reflexivity.
  - destruct b; simpl in Hx; try reflexivity; discriminate Hx.
  - destruct Hx.
Qed.

Lemma map_apply_phi_es_fixed : forall phi l,
  (forall x, In x l -> apes_fixed x) ->
  List.map (apply_phi_es phi) l = l.
Proof.
  intros phi l Hl.
  induction l; simpl.
  - reflexivity.
  - f_equal.
    + eapply apply_phi_es_fixed; [exact (Hl a (or_introl eq_refl))].
    + eapply IHl; intros x Hx; exact (Hl x (or_intror Hx)).
Qed.

Lemma apply_phi_es_preimage : forall phi x y,
  apply_phi_es phi x = y ->
  apes_fixed y ->
  x = y.
Proof.
  intros phi x y Hxy Hy.
  destruct x; simpl in Hxy; subst y; simpl in Hy; try reflexivity.
  - f_equal. eapply apply_phi_preserves; [reflexivity | exact Hy].
  - destruct Hy.
Qed.

Lemma map_apply_phi_es_fixed_inv : forall phi es_src e,
  List.map (apply_phi_es phi) es_src = e ->
  (forall x, In x e -> apes_fixed x) ->
  es_src = e.
Proof.
  intros phi es_src e H Hf.
  revert e H Hf.
  induction es_src as [|a es_src' IH]; intros e H Hf.
  - simpl in H. rewrite H. reflexivity.
  - simpl in H. destruct e; [discriminate H |].
    injection H as H1 Hrest.
    f_equal.
    + eapply apply_phi_es_preimage; [exact H1 | exact (Hf a0 (or_introl eq_refl))].
    + eapply IH; [exact Hrest | intros x Hx; exact (Hf x (or_intror Hx))].
Qed.

(* Any reduce_simple step whose input and output lists are apes_fixed can be
   replayed unchanged: the pointwise-preimage source list equals the target
   input, and the (fixed) output is its own preimage. *)
Lemma reduce_simple_ctx_fixed : forall phi es_src e e',
  List.map (apply_phi_es phi) es_src = e ->
  reduce_simple e e' ->
  (forall x, In x e -> apes_fixed x) ->
  (forall x, In x e' -> apes_fixed x) ->
  exists es_src',
    reduce_simple es_src es_src' /\
    List.map (apply_phi_es phi) es_src' = e'.
Proof.
  intros phi es_src e e' Hmap Hred Hfe Hfe'.
  rewrite (map_apply_phi_es_fixed_inv phi es_src e Hmap Hfe).
  exists e'. split.
  - exact Hred.
  - eapply map_apply_phi_es_fixed; exact Hfe'.
Qed.

Lemma apes_fixed_v_to_e : forall v, apes_fixed (v_to_e v).
Proof.
  intros v. destruct v as [vn | vv | vr]; simpl; try reflexivity.
  destruct vr as [rt | fa | ea]; simpl; reflexivity.
Qed.

Lemma apes_fixed_v_to_e_list : forall vs x, In x (v_to_e_list vs) -> apes_fixed x.
Proof.
  intros vs. induction vs as [|v vs' IH]; intros x Hx; simpl in Hx.
  - destruct Hx.
  - destruct Hx as [Hx | Hx].
    + subst x. apply apes_fixed_v_to_e.
    + exact (IH x Hx).
Qed.

Lemma apes_fixed_result_to_stack : forall r x, In x (result_to_stack r) -> apes_fixed x.
Proof.
  intros r x Hx. destruct r; simpl in Hx.
  - eapply apes_fixed_v_to_e_list; exact Hx.
  - destruct Hx as [Hx | Hx]; [subst x; exact I | destruct Hx].
Qed.

Lemma apes_fixed_app : forall l1 l2,
  (forall x, In x l1 -> apes_fixed x) ->
  (forall x, In x l2 -> apes_fixed x) ->
  forall x, In x (l1 ++ l2) -> apes_fixed x.
Proof.
  intros l1 l2 H1 H2 x Hx.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact (H1 x Hx) | exact (H2 x Hx)].
Qed.

Lemma const_list_fixed : forall es,
  is_true (const_list es) ->
  forall x, In x es -> apes_fixed x.
Proof.
  intros es H x Hx.
  assert (Hc : is_const x = true).
  { eapply const_list_in; [exact H | exact Hx]. }
  destruct x; simpl in Hc; try (simpl; discriminate Hc).
  - destruct b; simpl in Hc; try discriminate Hc; reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma apes_fixed_cat : forall (l1 l2 : list administrative_instruction),
  (forall x, In x l1 -> apes_fixed x) ->
  (forall x, In x l2 -> apes_fixed x) ->
  forall x, In x (seq.cat l1 l2) -> apes_fixed x.
Proof.
  intros l1 l2 H1 H2 x Hx.
  induction l1 as [|a l1' IH]; simpl in Hx.
  - exact (H2 x Hx).
  - destruct Hx as [Hx | Hx].
    + subst a. exact (H1 x (or_introl eq_refl)).
    + apply IH; [ intros y Hy; exact (H1 y (or_intror Hy)) | exact Hx ].
Qed.

(* Discharges a goal [forall x, In x l -> apes_fixed x] for a concrete list l,
   possibly containing v_to_e_list segments. *)
(* apply apes_fixed_v_to_e must be tried *before* simpl: on an abstract
   value (e.g. $V VAL_ref tabv) simpl unfolds v_to_e into a match on the
   reference and the lemma no longer applies. *)
Ltac apes_fixed_atom :=
  first [ apply apes_fixed_v_to_e
        | exact I
        | reflexivity
        | simpl; first [ apply apes_fixed_v_to_e | reflexivity | exact I ] ].

Ltac apes_fixed_base :=
  first
  [ apply apes_fixed_v_to_e_list
  | apply apes_fixed_result_to_stack
  | solve [ eapply const_list_fixed; eassumption ]
  (* cbn [In] rather than simpl: simpl would also unfold v_to_e on an
     abstract value, after which apes_fixed_v_to_e no longer applies. *)
  | intros apes_y apes_Hy; cbn [In] in apes_Hy;
    repeat match goal with
           | apes_Hy : _ \/ _ |- _ =>
               destruct apes_Hy as [apes_Hy | apes_Hy];
               [ try (subst apes_y); apes_fixed_atom | ]
           end;
    try contradiction;
    try (subst apes_y); apes_fixed_atom ].

(* The Wasm semantics states its instruction lists with ssreflect's seq.cat,
   while ListNotations' ++ is List.app here; both split shapes are tried. *)
Ltac apes_fixed_membership :=
  first
  [ apes_fixed_base
  | apply apes_fixed_app; [ apes_fixed_base | apes_fixed_base ]
  | apply apes_fixed_cat; [ apes_fixed_base | apes_fixed_base ] ].

(* A const list is a fixed point of the pointwise map: values carry no
   local indices for phi to rename. *)
Lemma map_apply_phi_es_const : forall phi vs,
  is_true (const_list vs) ->
  List.map (apply_phi_es phi) vs = vs.
Proof.
  intros phi vs Hc.
  eapply map_apply_phi_es_fixed.
  intros y Hy. eapply const_list_fixed; [exact Hc | exact Hy].
Qed.

(* List-level inversions, composing map_singleton_inv / map_cons_inv with
   the element-level ones.  Stating them once as propositions keeps the
   rs_label_* / rs_br and rs_if_* cases from each replaying the same
   destructuring tactic sequence. *)
Lemma map_apply_phi_es_label_inv : forall phi es_src n b c,
  List.map (apply_phi_es phi) es_src = [AI_label n b c] ->
  exists b' c', es_src = [AI_label n b' c'] /\
    List.map (apply_phi_es phi) b' = b /\
    List.map (apply_phi_es phi) c' = c.
Proof.
  intros phi es_src n b c H.
  apply map_singleton_inv in H. destruct H as [e0 [Hsrc He0]].
  apply apply_phi_es_label_inv in He0. destruct He0 as [b' [c' [Hlbl [Hb Hc]]]].
  exists b', c'. subst e0. exact (conj Hsrc (conj Hb Hc)).
Qed.

Lemma map_apply_phi_es_if_inv : forall phi es_src v tb es1 es2,
  List.map (apply_phi_es phi) es_src = [v_to_e v; AI_basic (BI_if tb es1 es2)] ->
  exists es1' es2',
    es_src = [v_to_e v; AI_basic (BI_if tb es1' es2')] /\
    List.map (apply_phi phi) es1' = es1 /\
    List.map (apply_phi phi) es2' = es2.
Proof.
  intros phi es_src v tb es1 es2 H.
  apply map_cons_inv in H. destruct H as [e0 [t [Hsrc [He0 Ht]]]].
  assert (He0' : e0 = v_to_e v).
  { exact (apply_phi_es_v_to_e_inv phi e0 v He0). }
  apply map_singleton_inv in Ht. destruct Ht as [e1 [Ht1 He1]].
  apply apply_phi_es_if_inv in He1. destruct He1 as [es1' [es2' [Hif [H1 H2]]]].
  exists es1', es2'. subst e0. subst e1. subst t.
  exact (conj Hsrc (conj H1 H2)).
Qed.

Lemma map_apply_phi_es_const_inv : forall phi c vs,
  List.map (apply_phi_es phi) c = vs ->
  is_true (const_list vs) ->
  c = vs.
Proof.
  intros phi c vs H Hc.
  eapply map_apply_phi_es_fixed_inv; [exact H |].
  intros x Hx. eapply const_list_fixed. exact Hc. exact Hx.
Qed.

Lemma apply_phi_es_local_tee_inv : forall phi e i,
  apply_phi_es phi e = AI_basic (BI_local_tee i) ->
  exists i', e = AI_basic (BI_local_tee i') /\ apply_phi_local phi i' = i.
Proof.
  intros phi e i H. destruct e; simpl in H; try (discriminate H).
  injection H as Hb.
  destruct b; simpl in Hb; try discriminate Hb.
  injection Hb as Hi.
  exists l. exact (conj eq_refl Hi).
Qed.

(* A pointwise preimage of a const-prefix + singleton is the same shape. *)
Lemma map_apply_phi_es_to_e_list : forall phi es' es,
  List.map (apply_phi phi) es' = es ->
  List.map (apply_phi_es phi) (to_e_list es') = to_e_list es.
Proof.
  intros phi es' es H.
  revert es H.
  induction es' as [|b es'' IH]; intros es H.
  - simpl in H. subst es. reflexivity.
  - simpl in H. destruct es as [|b0 es0]; [discriminate H |].
    injection H as Hb Hrest.
    simpl. f_equal.
    + apply f_equal. exact Hb.
    + exact (IH es0 Hrest).
Qed.
Lemma map_apply_phi_es_const_dspl : forall phi vs e l,
  List.map (apply_phi_es phi) l = vs ++ [e] ->
  is_true (const_list vs) ->
  exists e', l = vs ++ [e'] /\ apply_phi_es phi e' = e.
Proof.
  intros phi vs e l H Hc.
  destruct (map_app_split3 _ _ (apply_phi_es phi) l vs [e] [] H)
    as [l1 [l2 [l3 [Hl [H1 [H2 H3]]]]]].
  rewrite Hl.
  assert (Hl1 : l1 = vs).
  { eapply map_apply_phi_es_const_inv; [exact H1 | exact Hc]. }
  destruct (map_singleton_inv _ _ (apply_phi_es phi) l2 e H2) as [x [Hl2 Hx]].
  assert (Hl3 : l3 = []).
  { apply map_eq_nil_l in H3. exact H3. }
  rewrite Hl1. rewrite Hl2. rewrite Hl3.
  exists x. split; [reflexivity | exact Hx].
Qed.

(* A pointwise preimage of `vs ++ [AI_basic (BI_br i)]` (vs const) is that
   exact list: values br are fixed points. *)
Lemma map_apply_phi_es_const_br : forall phi vs i l,
  List.map (apply_phi_es phi) l = vs ++ [AI_basic (BI_br i)] ->
  is_true (const_list vs) ->
  l = vs ++ [AI_basic (BI_br i)].
Proof.
  intros phi vs i l H Hc.
  destruct (map_app_split3 _ _ (apply_phi_es phi) l vs [AI_basic (BI_br i)] [] H)
    as [l1 [l2 [l3 [Hl [H1 [H2 H3]]]]]].
  rewrite Hl.
  assert (Hl1 : l1 = vs).
  { eapply map_apply_phi_es_const_inv; [exact H1 | exact Hc]. }
  assert (Hl2' : exists x, l2 = [x] /\ apply_phi_es phi x = AI_basic (BI_br i)).
  { exact (map_singleton_inv _ _ (apply_phi_es phi) l2 (AI_basic (BI_br i)) H2). }
  destruct Hl2' as [x [Hl2 Hx]].
  assert (Hl2eq : l2 = [AI_basic (BI_br i)]).
  { rewrite Hl2. f_equal. eapply apply_phi_es_basic_inv_eq; [exact Hx | reflexivity]. }
  assert (Hl3 : l3 = []).
  { apply map_eq_nil_l in H3. exact H3. }
  rewrite Hl1 Hl2eq Hl3. reflexivity.
Qed.

(* A pointwise-apply_phi_es preimage of a reduce_simple step is a
   reduce_simple step whose output is again a pointwise image. *)
Lemma ctx_reduce_simple : forall phi es_src e e',
  List.map (apply_phi_es phi) es_src = e ->
  reduce_simple e e' ->
  exists es_src',
    reduce_simple es_src es_src' /\
    List.map (apply_phi_es phi) es_src' = e'.
Proof.
  intros phi es_src e e' Hrel Hred.
  revert es_src Hrel.
  induction Hred; intros es_src Hrel.
  all: try (solve [ eapply reduce_simple_ctx_fixed;
                    [ exact Hrel
                    | econstructor; eauto
                    | apes_fixed_membership | apes_fixed_membership ] ]).
  (* rs_ref_is_null_false is discharged by the blanket fixed-case tactic. *)
  (* ── rs_label_const ── *)
  - { destruct (map_apply_phi_es_label_inv phi es_src _ _ _ Hrel)
        as [b' [c' [Hsrc [Hb Hc]]]]. subst es_src.
      assert (Hcv : c' = vs).
      { eapply map_apply_phi_es_const_inv; [exact Hc | exact H]. }
      subst c'.
      exists vs. split.
      + apply rs_label_const. exact H.
      + exact (map_apply_phi_es_const phi vs H). }
  (* ── rs_label_trap ── *)
  - { destruct (map_apply_phi_es_label_inv phi es_src _ _ _ Hrel)
        as [b' [c' [Hsrc [Hb Hc]]]]. subst es_src.
      assert (Hcv : c' = [AI_trap]).
      { eapply map_apply_phi_es_fixed_inv; [exact Hc | apes_fixed_membership]. }
      subst c'.
      exists [AI_trap]. split.
      + apply rs_label_trap.
      + reflexivity. }
  (* ── rs_if_false ── *)
  - { destruct (map_apply_phi_es_if_inv phi es_src (VAL_num (VAL_int32 c)) tb es1 es2 Hrel)
        as [es1' [es2' [Hsrc [Hbp1 Hbp2]]]]. subst es_src.
      exists [AI_basic (BI_block tb es2')]. split.
      + apply rs_if_false. exact H. 
      + simpl. rewrite Hbp2. reflexivity. }
  (* ── rs_if_true ── *)
  - { destruct (map_apply_phi_es_if_inv phi es_src (VAL_num (VAL_int32 c)) tb es1 es2 Hrel)
        as [es1' [es2' [Hsrc [Hbp1 Hbp2]]]]. subst es_src.
      exists [AI_basic (BI_block tb es1')]. split.
      + apply rs_if_true. exact H.
      + simpl. rewrite Hbp1. reflexivity. }
  (* ── rs_br ── *)
  - { destruct (map_apply_phi_es_label_inv phi es_src _ _ _ Hrel)
        as [b' [c' [Hsrc [Hb Hc]]]]. subst es_src.
      assert (Hpre : exists (lh_src : lholed i),
                 c' = lfill lh_src (vs ++ [AI_basic (BI_br (N.of_nat i))])).
      { (* c' is the pointwise preimage of LI = lfill lh (vs ++ [br]) *)
        assert (Hrelc : List.map (apply_phi_es phi) c' = lfill lh (vs ++ [AI_basic (BI_br (N.of_nat i))])).
        { rewrite H1. exact Hc. }
        destruct (lfill_preimage phi i lh c' (vs ++ [AI_basic (BI_br (N.of_nat i))]) Hrelc)
          as [lh_src [es_inner [Hlh [Hcf Hrelin]]]].
        exists lh_src.
        assert (Hin := map_apply_phi_es_const_br phi vs (N.of_nat i) es_inner Hrelin H).
        rewrite <- Hin. exact Hcf. }
      destruct Hpre as [lh_src Hcf].
      exists (vs ++ b'). split.
      + apply rs_br with (n := n) (lh := lh_src).
        * exact H.
        * exact H0.
        * exact (eq_sym Hcf).
      + rewrite List.map_app.
        rewrite (map_apply_phi_es_const phi vs H). rewrite Hb. reflexivity. }
  (* rs_local_const and rs_local_trap are now discharged by the blanket
     fixed-case tactic above: AI_frame is apes_fixed since apply_phi_es
     leaves frames verbatim, and a const output list is fixed too. *)
  (* ── rs_local_tee ── *)
  - { apply map_cons_inv in Hrel. destruct Hrel as [e0 [t [Hsrc [He0 Ht]]]].
      assert (He0' : e0 = $V v).
      { exact (apply_phi_es_v_to_e_inv phi e0 v He0). }
      subst e0.
      apply map_singleton_inv in Ht. destruct Ht as [e1 [Ht1 He1]]. subst t.
      apply apply_phi_es_local_tee_inv in He1. destruct He1 as [i' [Hbb' Hi']]. subst e1.
      subst es_src.
      exists [$V v; $V v; AI_basic (BI_local_set i')]. split.
      + apply rs_local_tee.
      + simpl. congruence. }
  (* rs_return is likewise discharged by the blanket tactic. *)
  (* ── rs_trap ── *)
  - { assert (Hex : exists (lh_src : lholed 0),
               es_src = lfill lh_src [AI_trap]).
      { (* es = lfill lh [AI_trap], and es_src is a pointwise preimage *)
        rewrite <- H0 in Hrel.
        destruct (lfill_preimage phi 0 lh es_src [AI_trap] Hrel)
          as [lh_src [es_inner [Hlh [Heqf Hrelin]]]].
        exists lh_src.
        assert (Hin : es_inner = [AI_trap]).
        { eapply map_apply_phi_es_fixed_inv; [exact Hrelin | apes_fixed_membership]. }
        rewrite Hin in Heqf. exact Heqf. }
      destruct Hex as [lh_src Heqf].
      exists [AI_trap]. split.
      + apply rs_trap with (lh := lh_src).
        * intro Habs. apply H. rewrite <- Hrel. rewrite Habs. reflexivity.
        * exact (eq_sym Heqf).
      + reflexivity. }
Qed.

(* ── Blanket tactic for the "fixed" reduce constructors ──────────────
   The bulk of reduce's 70 constructors (table / memory / load / store /
   global / call-indirect / invoke) take an input list built only from
   values and non-complex basic instructions, leave the frame alone, and
   consult the frame solely through f_inst.  For those, apply_phi_es is the
   identity on both the input and the output list, so the source list *is*
   the target list and the very same constructor fires on the source side
   after rewriting f_inst f_src = f_inst f.  *)
Ltac ctx_src_eq :=
  match goal with
  | Hrel : List.map (apply_phi_es _) ?es_src = _ |- _ =>
      repeat (match goal with
              | H : _ = v_to_e_list _ |- _ => rewrite H in Hrel
              end);
      apply map_apply_phi_es_fixed_inv in Hrel;
      [ subst es_src | apes_fixed_membership ]
  end.

Ltac ctx_fixed_case fsrc Hi Hp Hl :=
  ctx_src_eq;
  exists fsrc; eexists; split; [| split];
  [ econstructor;
    solve [ rewrite ?Hi; eassumption
          | reflexivity
          | eapply reduce_call_transport; [ eassumption | exact Hi ]
          | eapply reduce_call_indirect_success_transport; [ eassumption | exact Hi ]
          | eapply reduce_call_indirect_failure_transport; [ eassumption | exact Hi ] ]
  | apply map_apply_phi_es_fixed; apes_fixed_membership
  | unfold frames_rel; exact (conj Hi (conj Hp Hl)) ].

Theorem coalesce_func_correct_ctx :
  forall phi (f_src : frame) (f_opt : frame),
    frames_rel phi f_src f_opt ->
    (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
       apply_phi_local phi i' = i ->
       N.to_nat i < length locs_opt ->
       R_phi phi locs_src locs_opt ->
       R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
                 (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
    forall hs s hs' s' es_src es_opt (f_opt' : frame) es_opt',
      List.map (apply_phi_es phi) es_src = es_opt ->
      reduce hs s f_opt es_opt hs' s' f_opt' es_opt' ->
      exists (f_src' : frame) es_src',
        reduce hs s f_src es_src hs' s' f_src' es_src' /\
        List.map (apply_phi_es phi) es_src' = es_opt' /\
        frames_rel phi f_src' f_opt'.
Proof.
  intros phi f_src f_opt Hfr Hset.
  destruct Hfr as [Hinst [Hphi Hlocal]].
  intros hs s hs' s' es_src es_opt f_opt' es_opt' Hrel Hred.
  revert es_src Hrel.
  induction Hred; intros es_src Hrel.
  all: try (solve [ ctx_fixed_case f_src Hinst Hphi Hlocal ]).

  (** ── r_simple ── **)
  - { destruct (ctx_reduce_simple phi es_src e e' Hrel H) as [es_src' [Hreds Hmap']].
      exists f_src, es_src'. split; [| split].
      + apply r_simple. exact Hreds.
      + exact Hmap'.
      + exact (conj Hinst (conj Hphi Hlocal)). }

  (* r_ref_func is discharged by the blanket fixed-case tactic. *)

  (** ── r_block ── **)
  - { destruct (map_apply_phi_es_const_dspl phi vs (AI_basic (BI_block tb es)) es_src Hrel H0)
        as [e0 [Hesrc He0]].
      subst es_src.
      apply apply_phi_es_block_inv in He0. destruct He0 as [es' [Hbb' Hes']]. subst e0.
      exists f_src, [AI_label m [] (vs ++ to_e_list es')]. split; [| split].
      + eapply r_block with (n := n) (t1s := t1s) (t2s := t2s).
        * rewrite <- Hinst in H. exact H.
        * exact H0.
        * exact H1.
        * exact H2.
        * exact H3.
      + simpl. f_equal. f_equal.
        rewrite List.map_app.
        rewrite (map_apply_phi_es_const phi vs H0).
        rewrite (map_apply_phi_es_to_e_list phi es' es Hes'). reflexivity.
      + exact (conj Hinst (conj Hphi Hlocal)). }

  (** ── r_loop ── **)
  - { destruct (map_apply_phi_es_const_dspl phi vs (AI_basic (BI_loop tb es)) es_src Hrel H0)
        as [e0 [Hesrc He0]].
      subst es_src.
      apply apply_phi_es_loop_inv in He0. destruct He0 as [es' [Hbb' Hes']]. subst e0.
      exists f_src, [AI_label n [AI_basic (BI_loop tb es')] (vs ++ to_e_list es')]. split; [| split].
      + eapply r_loop with (n := n) (m := m) (t1s := t1s) (t2s := t2s).
        * rewrite <- Hinst in H. exact H.
        * exact H0.
        * exact H1.
        * exact H2.
        * exact H3.
      + simpl. repeat f_equal.
        - exact Hes'.
        - rewrite List.map_app.
          rewrite (map_apply_phi_es_const phi vs H0).
          rewrite (map_apply_phi_es_to_e_list phi es' es Hes'). reflexivity.
      + exact (conj Hinst (conj Hphi Hlocal)). }

  (* r_call is discharged by the blanket fixed-case tactic. *)

  (** ── r_local_get ── **)
  - { apply map_singleton_inv in Hrel. destruct Hrel as [e0 [Hsrc He0]]. subst es_src.
      destruct (apply_phi_es_local_get_inv phi e0 j He0) as [i' [He0' Hmapi']].
      subst e0.
      assert (Hoob : N.to_nat (apply_phi_local phi i') < length (f_locs f)).
      { rewrite Hmapi'. unfold lookup_N in H.
        apply (proj1 (nth_error_Some (f_locs f) (N.to_nat j))).
        intro Hnone. rewrite H in Hnone. discriminate Hnone. }
      assert (Hbounds : N.to_nat i' < length (f_locs f_src)).
      { eapply Hlocal. exact Hoob. }
      assert (Hnth : nth_error (f_locs f_src) (N.to_nat i') = Some v).
      { rewrite (Hphi i' Hbounds). rewrite Hmapi'. unfold lookup_N in H. exact H. }
      exists f_src, [v_to_e v]. split; [| split].
      + apply r_local_get. unfold lookup_N. exact Hnth.
      + simpl. rewrite apply_phi_es_v_to_e. reflexivity.
      + exact (conj Hinst (conj Hphi Hlocal)). }

  (** ── r_local_set (the frame changes) ── **)
  - { apply map_cons_inv in Hrel. destruct Hrel as [e0 [t [Hsrc [He0 Ht]]]].
      assert (He0' : e0 = $V v).
      { exact (apply_phi_es_v_to_e_inv phi e0 v He0). }
      subst e0.
      apply map_singleton_inv in Ht. destruct Ht as [e1 [Ht1 He1]]. subst t.
      destruct (apply_phi_es_local_set_inv phi e1 i He1) as [i' [He1' Hmapi']].
      subst e1. subst es_src.
      assert (Hidden : N.to_nat i < length (f_locs f)).
      { destruct (@ssrnat.leP (S (N.to_nat i)) (length (f_locs f))) as [Hle | Hnle].
        - exact Hle.
        - exfalso. discriminate H0. }
      assert (Hbounds : N.to_nat i' < length (f_locs f_src)).
      { eapply Hlocal. rewrite Hmapi'. exact Hidden. }
      exists (Build_frame (seq.set_nth vd (f_locs f_src) (N.to_nat i') v)
                          (f_inst f_src)), [].
      split; [| split].
      + eapply r_local_set.
        * reflexivity.
        * destruct (@ssrnat.leP (S (N.to_nat i')) (length (f_locs f_src))) as [Hle | Hnle].
          - reflexivity.
          - exfalso. apply Hnle. exact Hbounds.
        * reflexivity.
      + reflexivity.
      + unfold frames_rel. simpl. rewrite H1. split; [| split].
        * rewrite H. exact Hinst.
        * eapply Hset; [exact Hmapi' | exact Hidden | exact Hphi].
        * intros i0 Hi0.
          rewrite (length_set_nth_lt vd (f_locs f_src) (N.to_nat i') v Hbounds).
          rewrite (length_set_nth_lt vd (f_locs f) (N.to_nat i) v Hidden) in Hi0.
          exact (Hlocal i0 Hi0). }

  (** ── r_label: the case the pointwise statement exists for ──
      The target steps under a label context, lfill lh es -> lfill lh es'.
      lfill_preimage inverts the source list into the same shape with a
      hole preimage; the (now fragment-level) IH fires on that hole; and
      apply_phi_es_lfill transports the result back out. *)
  - { subst les les'.
      destruct (lfill_preimage phi k lh es_src es Hrel)
        as [lh_src [es_inner [Hlh [Hsrceq Hrelin]]]].
      destruct (IHHred Hinst Hphi Hlocal es_inner Hrelin)
        as [f_src2 [es_inner' [Hred2 [Hmap2 Hphi2]]]].
      exists f_src2, (lfill lh_src es_inner'). split; [| split].
      + rewrite Hsrceq. eapply r_label with (lh := lh_src).
        * exact Hred2.
        * reflexivity.
        * reflexivity.
      + rewrite (apply_phi_es_lfill phi k lh_src es_inner').
        rewrite Hlh. rewrite Hmap2. reflexivity.
      + exact Hphi2. }
Qed.

(* ── Multi-step (reduce_trans) simulation ────────────────────────── *)

(* The pointwise relation lifted to whole configurations. *)
Definition sim_state (phi : local_map)
    (c_src c_opt : host_state * store_record * frame * list administrative_instruction)
    : Prop :=
  let '(hs1, s1, f1, es1) := c_src in
  let '(hs2, s2, f2, es2) := c_opt in
  hs1 = hs2 /\ s1 = s2 /\ frames_rel phi f1 f2 /\
  List.map (apply_phi_es phi) es1 = es2.

(* Closure of the pointwise simulation over arbitrary-length target traces.
   Every case of clos_refl_trans is immediate once the single-step theorem
   re-establishes the *whole* frame invariant (frames_rel), not just R_phi:
   that is what lets the invariant be threaded from one step to the next. *)
Lemma coalesce_trans_ctx : forall phi,
  (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
     apply_phi_local phi i' = i ->
     N.to_nat i < length locs_opt ->
     R_phi phi locs_src locs_opt ->
     R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
               (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
  forall c_opt c_opt', reduce_trans c_opt c_opt' ->
  forall c_src, sim_state phi c_src c_opt ->
  exists c_src', reduce_trans c_src c_src' /\ sim_state phi c_src' c_opt'.
Proof.
  intros phi Hset c_opt c_opt' Hred.
  induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz]; intros c_src Hsim.
  - (* rt_step *)
    destruct x as [[[hs s] f_opt] es_opt].
    destruct y as [[[hs' s'] f_opt'] es_opt'].
    destruct c_src as [[[hs1 s1] f_src] es_src].
    destruct Hsim as [Hhs [Hs [Hfr Hmap]]]. subst hs1. subst s1.
    simpl in Hstep.
    destruct (coalesce_func_correct_ctx phi f_src f_opt Hfr Hset
                hs s hs' s' es_src es_opt f_opt' es_opt' Hmap Hstep)
      as [f_src' [es_src' [Hred' [Hmap' Hfr']]]].
    exists (hs', s', f_src', es_src'). split.
    + apply Relation_Operators.rt_step. simpl. exact Hred'.
    + simpl. exact (conj eq_refl (conj eq_refl (conj Hfr' Hmap'))).
  - (* rt_refl *)
    exists c_src. split; [apply Relation_Operators.rt_refl | exact Hsim].
  - (* rt_trans *)
    destruct (IHxy c_src Hsim) as [c_mid [Hfst Hsimmid]].
    destruct (IHyz c_mid Hsimmid) as [c_src' [Hsnd Hsim']].
    exists c_src'. split; [| exact Hsim'].
    eapply Relation_Operators.rt_trans; [exact Hfst | exact Hsnd].
Qed.

Lemma map_apply_phi_es_AI_basic : forall phi bs,
  List.map (apply_phi_es phi) (List.map AI_basic bs) =
  List.map AI_basic (List.map (apply_phi phi) bs).
Proof.
  intros phi bs. induction bs as [|b bs' IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Theorem coalesce_func_correct_trans :
  forall phi f hs hs' s s' f_src f_opt f_opt' es_opt',
    f_inst f_src = f_inst f_opt ->
    R_phi phi (f_locs f_src) (f_locs f_opt) ->
    (forall i : N,
       N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
       N.to_nat i < length (f_locs f_src)) ->
    (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
       apply_phi_local phi i' = i ->
       N.to_nat i < length locs_opt ->
       R_phi phi locs_src locs_opt ->
       R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
                 (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
    reduce_trans
      (hs, s, f_opt,
       List.map AI_basic (List.map (apply_phi phi) (modfunc_body f)))
      (hs', s', f_opt', es_opt') ->
    exists f_src' es_src',
      reduce_trans
        (hs, s, f_src, List.map AI_basic (modfunc_body f))
        (hs', s', f_src', es_src') /\
      List.map (apply_phi_es phi) es_src' = es_opt' /\
      R_phi phi (f_locs f_src') (f_locs f_opt').
Proof.
  intros phi f hs hs' s s' f_src f_opt f_opt' es_opt' Hinst Hphi Hlocal Hset Htrans.
  assert (Hsim0 : sim_state phi
            (hs, s, f_src, List.map AI_basic (modfunc_body f))
            (hs, s, f_opt,
             List.map AI_basic (List.map (apply_phi phi) (modfunc_body f)))).
  { simpl. refine (conj eq_refl (conj eq_refl (conj _ _))).
    - exact (conj Hinst (conj Hphi Hlocal)).
    - apply map_apply_phi_es_AI_basic. }
  destruct (coalesce_trans_ctx phi Hset _ _ Htrans _ Hsim0)
    as [c_src' [Hred' Hsim']].
  destruct c_src' as [[[hs2 s2] f_src'] es_src'].
  destruct Hsim' as [Hhs2 [Hs2 [Hfr' Hmap']]]. subst hs2. subst s2.
  exists f_src', es_src'. split; [| split].
  - exact Hred'.
  - exact Hmap'.
  - destruct Hfr' as [_ [Hp _]]. exact Hp.
Qed.

(* ── The pass instantiated at its own phi ──────────────────────────
   coalesce_func_correct_trans quantifies over an arbitrary phi, so on its
   own it says nothing about the map the pass actually computes.  This
   corollary pins phi to compute_phi's output and states the conclusion
   about coalesce_func itself; modfunc_body (coalesce_func pc n f) is
   convertible to List.map (apply_phi phi) (modfunc_body f).

   CAVEAT.  The Hset premise is *not* discharged here, and it cannot be:
   R_phi forces any two source locals sharing a target slot to hold equal
   values (see the note on R_phi above), so Hset is false as soon as phi
   merges two locals that ever differ.  This corollary therefore has real
   content only when compute_phi returns an injective map -- in particular
   when it rejects the function and returns `empty` (see
   coalesce_func_rejected_id).  Making it bite for genuine coalescing
   needs a weaker invariant, keyed on which local is live rather than on
   all merged locals agreeing. *)
Corollary coalesce_func_correct_compute_phi :
  forall tys pc n f hs hs' s s' f_src f_opt f_opt' es_opt',
    let phi := compute_phi tys pc n (modfunc_body f) in
    f_inst f_src = f_inst f_opt ->
    R_phi phi (f_locs f_src) (f_locs f_opt) ->
    (forall i : N,
       N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
       N.to_nat i < length (f_locs f_src)) ->
    (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
       apply_phi_local phi i' = i ->
       N.to_nat i < length locs_opt ->
       R_phi phi locs_src locs_opt ->
       R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
                 (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
    reduce_trans
      (hs, s, f_opt,
       List.map AI_basic (modfunc_body (coalesce_func tys pc n f)))
      (hs', s', f_opt', es_opt') ->
    exists f_src' es_src',
      reduce_trans
        (hs, s, f_src, List.map AI_basic (modfunc_body f))
        (hs', s', f_src', es_src') /\
      List.map (apply_phi_es phi) es_src' = es_opt' /\
      R_phi phi (f_locs f_src') (f_locs f_opt').
Proof.
  intros tys pc n f hs hs' s s' f_src f_opt f_opt' es_opt' phi
         Hinst Hphi Hlocal Hset Hred.
  eapply coalesce_func_correct_trans;
    [ exact Hinst | exact Hphi | exact Hlocal | exact Hset | exact Hred ].
Qed.

(* ── The whole-body single-step statement, as a corollary of ctx ────
   The statement a direct induction cannot reach (it stalls at r_label --
   a whole-body IH cannot step the inner fragment of a label context).
   Derived from the pointwise theorem it is three lines and carries no
   admits, so the two corollaries below are axiom-free as well. *)
Theorem coalesce_func_correct_body :
  forall phi f hs hs' s s' f_src f_opt f_opt' es',
    f_inst f_src = f_inst f_opt ->
    R_phi phi (f_locs f_src) (f_locs f_opt) ->
    (forall i : N,
       N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
       N.to_nat i < length (f_locs f_src)) ->
    (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
       apply_phi_local phi i' = i ->
       N.to_nat i < length locs_opt ->
       R_phi phi locs_src locs_opt ->
       R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
                 (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
    reduce hs s f_opt
           (List.map AI_basic (List.map (apply_phi phi) f.(modfunc_body)))
           hs' s' f_opt' es' ->
    exists f_src' es0,
      reduce hs s f_src (List.map AI_basic f.(modfunc_body))
             hs' s' f_src' es0 /\
      R_phi phi (f_locs f_src') (f_locs f_opt').
Proof.
  intros phi f hs hs' s s' f_src f_opt f_opt' es' Hinst Hphi Hlocal Hset Hred.
  destruct (coalesce_func_correct_ctx phi f_src f_opt
              (conj Hinst (conj Hphi Hlocal)) Hset
              hs s hs' s'
              (List.map AI_basic (modfunc_body f))
              (List.map AI_basic (List.map (apply_phi phi) (modfunc_body f)))
              f_opt' es'
              (map_apply_phi_es_AI_basic phi (modfunc_body f)) Hred)
    as [f_src' [es_src' [Hred' [_ Hfr']]]].
  exists f_src', es_src'. split; [exact Hred' |].
  destruct Hfr' as [_ [Hp _]]. exact Hp.
Qed.

Theorem coalesce_func_correct_all : forall phi m f,
    In f m.(mod_funcs) ->
    forall hs hs' s s' f_src f_opt f_opt' es',
      f_inst f_src = f_inst f_opt ->
      R_phi phi (f_locs f_src) (f_locs f_opt) ->
      (forall i : N,
         N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
         N.to_nat i < length (f_locs f_src)) ->
      (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
         apply_phi_local phi i' = i ->
         N.to_nat i < length locs_opt ->
         R_phi phi locs_src locs_opt ->
         R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
                   (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
      reduce hs s f_opt
             (List.map AI_basic (List.map (apply_phi phi) f.(modfunc_body)))
             hs' s' f_opt' es' ->
      exists f_src' es0,
        reduce hs s f_src (List.map AI_basic f.(modfunc_body))
               hs' s' f_src' es0 /\
        R_phi phi (f_locs f_src') (f_locs f_opt').
Proof.
  intros phi m f Hin hs hs' s s' f_src f_opt f_opt' es' Hinst Hphi Hlocal Hset Hred.
  exact (coalesce_func_correct_body phi f hs hs' s s' f_src f_opt f_opt' es'
           Hinst Hphi Hlocal Hset Hred).
Qed.

Theorem coalesce_func_correct_plain :
  forall phi f hs hs' s s' f_src f_opt f_opt' es',
    f_inst f_src = f_inst f_opt ->
    R_phi phi (f_locs f_src) (f_locs f_opt) ->
    (forall i : N,
       N.to_nat (apply_phi_local phi i) < length (f_locs f_opt) ->
       N.to_nat i < length (f_locs f_src)) ->
    (forall (v : value) (vd : value) (locs_src locs_opt : list value) (i i' : N),
       apply_phi_local phi i' = i ->
       N.to_nat i < length locs_opt ->
       R_phi phi locs_src locs_opt ->
       R_phi phi (seq.set_nth vd locs_src (N.to_nat i') v)
                 (seq.set_nth vd locs_opt (N.to_nat i) v)) ->
    (forall b, In b (modfunc_body f) -> apply_phi phi b = b) ->
    reduce hs s f_opt
           (List.map AI_basic (modfunc_body f))
           hs' s' f_opt' es' ->
    exists f_src' es0,
      reduce hs s f_src (List.map AI_basic (modfunc_body f))
             hs' s' f_src' es0 /\
      R_phi phi (f_locs f_src') (f_locs f_opt').
Proof.
  intros phi f hs hs' s s' f_src f_opt f_opt' es' Hinst Hphi Hlocal Hset Hfix Hred.
  eapply coalesce_func_correct_body.
  - exact Hinst.
  - exact Hphi.
  - exact Hlocal.
  - exact Hset.
  - rewrite (map_apply_phi_id phi (modfunc_body f) Hfix). exact Hred.
Qed.

(* ── Multi-step closure of the liveness-keyed simulation ───────────
   coalesce_trans_ctx above already closes a simulation under
   reduce_trans, but the one it closes is keyed on R_phi, which forces
   every pair of merged locals to hold equal values -- vacuous as soon
   as the pass does anything (see the CAVEAT on
   coalesce_func_correct_compute_phi).  sim_step is the simulation with
   content; what follows closes *that* one.

   The only thing that does not thread for free is store_guarded.
   sim_step needs it at every step, because r_invoke_native relates a
   fresh activation of a callee whose body comes from the store, and
   that body has to satisfy the nesting restriction.  Every reduction
   rule but one leaves s_funcs alone: the store-changing rules touch
   memories, tables, globals, elems and datas, and each of them builds
   its new record with [s_funcs := s_funcs s].  The exception is
   r_invoke_host_success, where host_application hands back an
   arbitrary store (host.v) and could in principle install new code.

   So the host has to promise not to.  That is a real assumption and it
   is stated as one: a host that can install Wasm code invalidates any
   whole-program analysis, not just this pass.  CertiRocq's host does
   not have that power. *)

Definition host_keeps_funcs : Prop :=
  forall hs s tf h vcs hs' s' r,
    host_application hs s tf h vcs hs' (Some (s', r)) ->
    s_funcs s' = s_funcs s.

(* Each store update is a record literal that repeats [s_funcs s], so
   the whole family goes through by reducing the option plumbing away
   and reading the field off.  delta is restricted to the update
   functions themselves: a bare cbn would unfold into the memory
   backend. *)
Ltac store_funcs_solve :=
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

Lemma reduce_keeps_funcs : forall hs s f es hs' s' f' es',
  host_keeps_funcs ->
  reduce hs s f es hs' s' f' es' -> s_funcs s' = s_funcs s.
Proof.
  intros hs s f es hs' s' f' es' Hhost Hred.
  induction Hred; try reflexivity.
  all: try (solve [ exact (Hhost _ _ _ _ _ _ _ _ H5) ]).
  all: try (solve [ assumption ]).
  all: store_funcs_solve.
Qed.

(* store_guarded reads nothing but s_funcs, so it comes along. *)
Lemma reduce_store_guarded : forall hs s f es hs' s' f' es',
  host_keeps_funcs ->
  reduce hs s f es hs' s' f' es' -> store_guarded s -> store_guarded s'.
Proof.
  intros hs s f es hs' s' f' es' Hhost Hred Hg addr tf inst code Hlk.
  rewrite (reduce_keeps_funcs _ _ _ _ _ _ _ _ Hhost Hred) in Hlk.
  exact (Hg _ _ _ _ Hlk).
Qed.

Definition cfg_store
  (c : host_state * store_record * frame * list administrative_instruction)
  : store_record := let '(_, s, _, _) := c in s.

Lemma reduce_trans_store_guarded : forall c c',
  host_keeps_funcs -> reduce_trans c c' ->
  store_guarded (cfg_store c) -> store_guarded (cfg_store c').
Proof.
  intros c c' Hhost Hred. induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz];
    intros Hg.
  - destruct x as [[[hs s] f] es]. destruct y as [[[hs' s'] f'] es'].
    simpl in *. eapply reduce_store_guarded; eassumption.
  - exact Hg.
  - exact (IHyz (IHxy Hg)).
Qed.

(* sim_step's invariant, lifted to whole configurations.  hs and s are
   shared rather than related: the two runs use the same store, which
   is the standing limitation of this simulation -- a callee is invoked
   from s_funcs and so is *not* coalesced on either side. *)
Definition sim_cfg (phi : local_map) (K : N -> Prop)
    (c c_o : host_state * store_record * frame * list administrative_instruction)
    : Prop :=
  let '(hs, s, f, es) := c in
  let '(hs_o, s_o, f_o, es_o) := c_o in
  hs = hs_o /\ s = s_o /\ rel_es phi K es es_o
  /\ frames_agree phi (live_ext es K) f f_o.

(* Every case is immediate once store_guarded is available at the
   midpoint of rt_trans, because sim_step re-establishes rel_es and
   frames_agree at the *successor* liveness set, which is exactly what
   the next step needs. *)
Theorem sim_trans : forall phi K,
  host_keeps_funcs ->
  forall c c', reduce_trans c c' ->
    store_guarded (cfg_store c) ->
    forall c_o, sim_cfg phi K c c_o ->
    exists c_o', reduce_trans c_o c_o' /\ sim_cfg phi K c' c_o'.
Proof.
  intros phi K Hhost c c' Hred.
  induction Hred as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz];
    intros Hg c_o Hsim.
  - destruct x as [[[hs s] f] es]. destruct y as [[[hs' s'] f'] es'].
    destruct c_o as [[[hs_o s_o] f_o] es_o].
    destruct Hsim as [Hhs [Hs [Hrel Hfr]]]. subst hs_o. subst s_o.
    simpl in Hstep. simpl in Hg.
    destruct (sim_step _ _ _ _ _ _ _ _ Hstep Hg phi K f_o es_o Hrel Hfr)
      as [f_o' [es_o' [Hstep_o [Hrel' Hfr']]]].
    exists (hs', s', f_o', es_o'). split.
    + apply Relation_Operators.rt_step. simpl. exact Hstep_o.
    + simpl. exact (conj eq_refl (conj eq_refl (conj Hrel' Hfr'))).
  - exists c_o. split; [apply Relation_Operators.rt_refl | exact Hsim].
  - destruct (IHxy Hg c_o Hsim) as [c_mid [Hfst Hsimmid]].
    assert (Hgy : store_guarded (cfg_store y))
      by exact (reduce_trans_store_guarded _ _ Hhost Hxy Hg).
    destruct (IHyz Hgy c_mid Hsimmid) as [c_o' [Hsnd Hsim']].
    exists c_o'. split; [| exact Hsim'].
    eapply Relation_Operators.rt_trans; [exact Hfst | exact Hsnd].
Qed.

(* The form a caller wants: start from a function body and its
   coalesced counterpart, related by rel_bs at the empty continuation
   [fun _ => False] (nothing is live after the body), and run.  This is
   the multi-step statement that coalesce_func_with_types_related in
   alloc_correct.v feeds. *)
Theorem coalesce_body_trans :
  forall phi bs bs_o hs s f_src f_opt hs' s' f_src' es',
    host_keeps_funcs ->
    store_guarded s ->
    rel_bs phi (fun _ => False) bs bs_o ->
    frames_agree phi (bs_live_ext bs (fun _ => False)) f_src f_opt ->
    reduce_trans (hs, s, f_src, to_e_list bs) (hs', s', f_src', es') ->
    exists f_opt' es_o',
      reduce_trans (hs, s, f_opt, to_e_list bs_o) (hs', s', f_opt', es_o') /\
      rel_es phi (fun _ => False) es' es_o' /\
      frames_agree phi (live_ext es' (fun _ => False)) f_src' f_opt'.
Proof.
  intros phi bs bs_o hs s f_src f_opt hs' s' f_src' es' Hhost Hg Hbs Hfr Htrans.
  assert (Hsim0 : sim_cfg phi (fun _ => False)
                    (hs, s, f_src, to_e_list bs) (hs, s, f_opt, to_e_list bs_o)).
  { simpl. refine (conj eq_refl (conj eq_refl (conj _ _))).
    - apply rel_es_to_e_list. exact Hbs.
    - refine (frames_agree_sub _ _ _ _ _ _ Hfr).
      intros i Hi. apply live_ext_to_e_list. exact Hi. }
  destruct (sim_trans phi (fun _ => False) Hhost _ _ Htrans Hg _ Hsim0)
    as [c_o' [Hred_o Hsim']].
  destruct c_o' as [[[hs_o' s_o'] f_opt'] es_o'].
  destruct Hsim' as [Hhs [Hs [Hrel' Hfr']]]. subst hs_o'. subst s_o'.
  exists f_opt', es_o'. split; [| split].
  - exact Hred_o.
  - exact Hrel'.
  - exact Hfr'.
Qed.

End Correctness.
