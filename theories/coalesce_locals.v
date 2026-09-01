From Wasm Require Import datatypes datatypes_properties opsem.
From Stdlib Require Import FMapAVL OrderedTypeEx List.

Import Bool ssreflect BinNat ListNotations.

(* ── FMap for local-variable renaming ──────────────────────────── *)

Module M := FMapAVL.Make (N_as_OT).

Notation "x |-> y" := (M.add x y M.empty) (at level 60, no associativity).
Notation "x !! i" := (M.find i x) (at level 60, no associativity).

Definition local_map := M.t localidx.
Definition empty := M.empty localidx.

(* ── apply_phi (shape-preserving rename) ───────────────────────── *)

Definition apply_phi_local (phi : local_map) (i : localidx) : localidx :=
  match M.find i phi with
  | Some j => j
  | None   => i
  end.

Fixpoint apply_phi (phi : local_map) (i : basic_instruction) :
  basic_instruction :=
  match i with
  | BI_local_get idx  => BI_local_get (apply_phi_local phi idx)
  | BI_local_set idx  => BI_local_set (apply_phi_local phi idx)
  | BI_local_tee idx  => BI_local_tee (apply_phi_local phi idx)
  | BI_block bt b     => BI_block bt  (List.map (apply_phi phi) b)
  | BI_loop bt b      => BI_loop bt   (List.map (apply_phi phi) b)
  | BI_if bt b1 b2    => BI_if bt     (List.map (apply_phi phi) b1)
                                      (List.map (apply_phi phi) b2)
  | _                 => i
  end.

(* The rename alone, leaving the declared locals as they were.
   [coalesce_func] below is this plus the truncation; the two are kept
   apart because only the rename is shape-preserving, and it is the
   rename that the simulation is proved over. *)
Definition apply_phi_func (phi : local_map) (f : module_func) : module_func :=
  {| modfunc_type   := f.(modfunc_type);
     modfunc_locals := f.(modfunc_locals);
     modfunc_body   := List.map (apply_phi phi) f.(modfunc_body) |}.

Definition apply_phi_module (phi : local_map) (m : module) : module :=
  {| mod_types   := m.(mod_types);
     mod_funcs   := List.map (apply_phi_func phi) m.(mod_funcs);
     mod_tables  := m.(mod_tables);
     mod_mems    := m.(mod_mems);
     mod_globals := m.(mod_globals);
     mod_elems   := m.(mod_elems);
     mod_datas   := m.(mod_datas);
     mod_start   := m.(mod_start);
     mod_imports  := m.(mod_imports);
     mod_exports  := m.(mod_exports) |}.

(* ── Syntactic queries on a body ───────────────────────────────────
   Does a body write a local, and does it branch.  Both are used twice:
   here, to gate the walk below, and in coalesce_locals_correct.v, where
   the simulation relation asks for exactly [body_ok_b] on every
   structured body it descends into.  One definition, so the check the
   pass runs and the check the proof needs cannot drift apart.

   [BI_return] and [BI_return_call] are deliberately not branches: they
   leave the activation entirely, so no later read of these locals can
   run, and a kill they skip cannot matter.

   The nested [let fix] is forced by the guard checker: a Fixpoint
   alternating between basic_instruction and lists of them is not
   accepted. *)

Fixpoint bi_writes (b : basic_instruction) {struct b} : bool :=
  let fix bsw (bs : list basic_instruction) : bool :=
    match bs with
    | [] => false
    | b' :: rest => bi_writes b' || bsw rest
    end in
  match b with
  | BI_local_set _ => true
  | BI_local_tee _ => true
  | BI_block _ bs => bsw bs
  | BI_loop _ bs => bsw bs
  | BI_if _ b1 b2 => bsw b1 || bsw b2
  | _ => false
  end.

Fixpoint bs_writes (bs : list basic_instruction) : bool :=
  match bs with
  | [] => false
  | b :: rest => bi_writes b || bs_writes rest
  end.

Fixpoint bi_br (b : basic_instruction) {struct b} : bool :=
  let fix bsb (bs : list basic_instruction) : bool :=
    match bs with
    | [] => false
    | b' :: rest => bi_br b' || bsb rest
    end in
  match b with
  | BI_br _ => true
  | BI_br_if _ => true
  | BI_br_table _ _ => true
  | BI_block _ bs => bsb bs
  | BI_loop _ bs => bsb bs
  | BI_if _ b1 b2 => bsb b1 || bsb b2
  | _ => false
  end.

Fixpoint bs_br (bs : list basic_instruction) : bool :=
  match bs with
  | [] => false
  | b :: rest => bi_br b || bs_br rest
  end.

(* What a structured body must satisfy for a write inside it to be safe.
   A write is only safe if the body's kills really happen, and the one
   thing that can skip them is a branch out of (or back to the top of)
   the body: it jumps over a kill the liveness already counted.  So the
   body must have no branch, or no write. *)
Definition body_ok_b (bs : list basic_instruction) : bool :=
  negb (bs_br bs) || negb (bs_writes bs).

(* The nesting restriction the *relation* rests on, as opposed to the
   one the walk enforces: every structured body is branch-free or
   write-free.  It lives here rather than in the correctness file
   because [func_supported] checks it -- a function the walk rejects is
   left alone, and even then the simulation has to relate its body to
   itself, which needs this. *)
Definition bi_guarded (b : basic_instruction) : bool :=
  match b with
  | BI_block _ bs => body_ok_b bs
  | BI_loop _ bs  => body_ok_b bs
  | BI_if _ b1 b2 => body_ok_b b1 && body_ok_b b2
  | _ => true
  end.

Fixpoint bs_guarded (bs : list basic_instruction) : bool :=
  match bs with
  | [] => true
  | b :: rest => bi_guarded b && bs_guarded rest
  end.

Definition bi_kills (i : N) (b : basic_instruction) : bool :=
  match b with
  | BI_local_set j => N.eqb i j
  | BI_local_tee j => N.eqb i j
  | _ => false
  end.

(* The list recursion is inlined as a local fix rather than written as a
   mutual Fixpoint: Rocq's guard checker rejects mutual recursion that
   alternates between a type and lists of it.  bi_live_block / _loop / _if
   below recover the equations one would have written directly. *)
Fixpoint bi_live (i : N) (b : basic_instruction) {struct b} : bool :=
  let fix bsl (bs : list basic_instruction) : bool :=
    match bs with
    | [] => false
    | b' :: rest => bi_live i b' || (negb (bi_kills i b') && bsl rest)
    end in
  match b with
  | BI_local_get j => N.eqb i j
  | BI_block _ bs => bsl bs
  | BI_loop _ bs => bsl bs
  | BI_if _ b1 b2 => bsl b1 || bsl b2
  | _ => false
  end.

Fixpoint bs_live_b (i : N) (bs : list basic_instruction) : bool :=
  match bs with
  | [] => false
  | b :: rest => bi_live i b || (negb (bi_kills i b) && bs_live_b i rest)
  end.

Lemma bi_live_block : forall i bt bs, bi_live i (BI_block bt bs) = bs_live_b i bs.
Proof.
  intros i bt bs. induction bs as [|b rest IH]; simpl; [reflexivity |].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma bi_live_loop : forall i bt bs, bi_live i (BI_loop bt bs) = bs_live_b i bs.
Proof.
  intros i bt bs. induction bs as [|b rest IH]; simpl; [reflexivity |].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma bi_live_if : forall i bt b1 b2,
  bi_live i (BI_if bt b1 b2) = bs_live_b i b1 || bs_live_b i b2.
Proof.
  intros i bt b1 b2.
  rewrite <- (bi_live_block i bt b1). rewrite <- (bi_live_block i bt b2).
  reflexivity.
Qed.

Fixpoint bs_kills_b (i : N) (bs : list basic_instruction) : bool :=
  match bs with
  | [] => false
  | b :: rest => bi_kills i b || bs_kills_b i rest
  end.

(* The lists enclosing the body being walked, innermost first.  Kept as a
   stack rather than appended into one list so that pushing is a cons: the
   walk pushes one per nesting level, and an append at every instruction
   would be quadratic on a 47k-instruction function.

   [stack_read] asks whether *any* enclosing level reads the local, with
   no kill shadowing: a level that kills [i] does not stop the search at
   the levels outside it.

   Kill shadowing would be the sharper question -- a read beyond a kill
   cannot observe what happens here -- but it is the wrong one, because
   [bs_kills_b] and the liveness the simulation relation runs on disagree
   about nested writes.  [bs_kills_b] only sees a write at the top level
   of a list, so a body that writes [i] inside a nested block and then
   again at its own top level counts as killing [i] here while
   [bs_live_b] still reports [i] live across the whole construct from
   outside.  Shadowing on that kill would confine the nested write to its
   own position, and the interval would then start after an anchor that
   still has [i] live -- see the third regression case in
   examples/regression/README.md.  Ignoring kills is the conservative
   direction: it opens more intervals at 0, never fewer. *)
Fixpoint stack_read (i : N) (ls : list (list basic_instruction)) : bool :=
  match ls with
  | [] => false
  | bs :: rest => bs_live_b i bs || stack_read i rest
  end.

(* ── M1: forward interval-collection walk ──────────────────────── *)

Record walk_state := mk_ws {
  ws_pos   : nat;
  ws_defs  : M.t nat;   (* localidx  ↦  def_pos      *)
  ws_uses  : M.t nat;   (* localidx  ↦  last_use_pos  *)
  ws_ok    : bool;      (* false once a guard trips    *)
  ws_self  : list (list basic_instruction);
                        (* the lists enclosing the body being walked,
                           innermost first *)
  ws_encl  : list basic_instruction
                        (* the list the current instruction is in *)
}.

Definition ws_stacks (self : list (list basic_instruction))
  (encl : list basic_instruction) (st : walk_state) : walk_state :=
  mk_ws st.(ws_pos) st.(ws_defs) st.(ws_uses) st.(ws_ok) self encl.

(* The walk carries the structured-control nesting `depth`, but only its
   zero-ness matters: it decides where a local's live interval *starts*.

   The interval model reads a range off source order -- from the first def
   to the last touch -- and that is faithful only when the def dominates
   every later touch and runs at most once.  At depth 0 both hold.  A def
   under a block/loop/if has neither property in general: the branch may
   be skipped, so a later read can see the zero-initialised slot instead,
   and a loop re-runs the body, so a read textually *before* the write
   still observes it across iterations.

   Both failures are about reads the def does not reach.  If nothing
   outside the body reads the local, neither can be observed: a skipped
   def is a def of a local nobody goes on to read, and a re-entered body
   redefines before it reads.  So a nested def opens at its own position
   exactly when the local is dead outside the body, and at 0 otherwise --
   where it overlaps everything live before it and the allocator gives it
   a slot no one can reuse ahead of it.

   "Outside" has to mean outside in the *control* sense, not merely later
   in the text.  A local written in one arm of an `if` and read in the
   other is read on a path where the write never ran, so it is not dead
   outside its arm.  That is why [ws_self] holds whole enclosing lists
   rather than the parts of them still to run: [bi_live] descends into a
   construct, so a read in a sibling arm is seen, and [bs_kills_b] only
   shadows at the top level of a list, never inside a construct.  With
   suffixes instead, this miscompiles:

     (local i32 i32)  i32.const 42  local.set 1  local.get 1  drop
     local.get 0  if (result i32)  i32.const 7  local.set 2  i32.const 0
                  else  local.get 2  end

   -- local 2 looks dead after arm 1, takes local 1's slot, and f(0)
   returns 42 where it must return 0.  See examples/regression/arms.wat.

   Nothing is lost by widening to the whole list: the two differ only on
   a read *before* the construct, and a local whose first def is inside
   the body can have no such read, because a read before any def sets
   [ws_ok] false and the function is left alone.

   The test is [stack_read], not [stack_live]: see its definition above
   for why a kill in an enclosing list must not shadow a read outside
   it. *)
Fixpoint walk_instr
  (param_count n : N)
  (depth : nat)
  (st : walk_state)
  (i : basic_instruction) : walk_state :=
  let pos     := st.(ws_pos) in
  let st_base := mk_ws (pos + 1) st.(ws_defs) st.(ws_uses) st.(ws_ok)
                       st.(ws_self) st.(ws_encl) in
  let walk_list d a instrs :=
    List.fold_left (fun a' i' => walk_instr param_count n d a' i')
                   instrs a in
  (* entering a body whose branches could skip its own writes: give up *)
  let body_guard b st' :=
    if body_ok_b b then st'
    else mk_ws st'.(ws_pos) st'.(ws_defs) st'.(ws_uses) false
               st'.(ws_self) st'.(ws_encl) in
  let enter b st' := ws_stacks (st.(ws_encl) :: st.(ws_self)) b st' in
  let leave st'   := ws_stacks st.(ws_self) st.(ws_encl) st' in
  let def_instr idx :=
    if N.ltb idx param_count then st_base
    else if N.ltb idx n then
      let start :=
        match M.find idx st.(ws_defs) with
        | Some d => d                                (* keep the first def *)
        | None   => if Nat.eqb depth 0 then pos      (* dominating def     *)
                    else if stack_read idx st.(ws_self) then 0
                                                     (* read outside: entry *)
                    else pos                         (* dead outside it     *)
        end in
      mk_ws (pos + 1)
            (M.add idx start st.(ws_defs))
            (M.add idx pos   st.(ws_uses))           (* a write is a touch  *)
            st.(ws_ok) st.(ws_self) st.(ws_encl)
    else st_base in
  match i with
  | BI_local_get idx =>
    if N.ltb idx param_count then st_base            (* param -> skip  *)
    else if N.ltb idx n then
      if M.mem idx st.(ws_defs) then                 (* use after def *)
        mk_ws (pos + 1) st.(ws_defs)
              (M.add idx pos st.(ws_uses)) st.(ws_ok)
              st.(ws_self) st.(ws_encl)
      else                                           (* use before def *)
        mk_ws (pos + 1) st.(ws_defs) st.(ws_uses) false
              st.(ws_self) st.(ws_encl)
    else st_base

  | BI_local_set idx => def_instr idx
  | BI_local_tee idx => def_instr idx

  | BI_block _ b    => leave (walk_list (S depth) (enter b (body_guard b st_base)) b)
  | BI_loop _ b     => leave (walk_list (S depth) (enter b (body_guard b st_base)) b)
  | BI_if _ b1 b2   => let st0 := body_guard b2 (body_guard b1 st_base) in
                       let st1 := walk_list (S depth) (enter b1 st0) b1 in
                       leave (walk_list (S depth) (enter b2 st1) b2)
  | _               => st_base
  end.

Definition walk_func
  (param_count n : N)
  (body : list basic_instruction) : walk_state :=
  List.fold_left (fun a i => walk_instr param_count n 0 a i)
                 body (mk_ws 0 (M.empty nat) (M.empty nat) true [] body).

Definition coalescable
  (param_count n : N)
  (body : list basic_instruction) : bool :=
  (walk_func param_count n body).(ws_ok).

(* ── M2: linear scan → phi ─────────────────────────────────────── *)

Definition extract_intervals (st : walk_state) :
  list (localidx * nat * nat) :=
  List.map (fun '(idx, def_pos) =>
    let last_use_pos :=
      match M.find idx st.(ws_uses) with
      | Some p => p
      | None   => def_pos
      end in
    (idx, def_pos, last_use_pos)
  ) (M.elements st.(ws_defs)).

Fixpoint insert_by_def (x : localidx * nat * nat)
  (ys : list (localidx * nat * nat)) :
  list (localidx * nat * nat) :=
  match ys with
  | [] => [x]
  | y :: rest =>
    let '(_, da, _) := x in
    let '(_, dy, _) := y in
    if Nat.leb da dy then x :: ys
    else y :: insert_by_def x rest
  end.

Fixpoint sort_by_def (intervals : list (localidx * nat * nat)) :
  list (localidx * nat * nat) :=
  match intervals with
  | [] => []
  | x :: rest => insert_by_def x (sort_by_def rest)
  end.

Definition slot_used_by_active (slot : N) (active : list (N * nat)) :
  bool :=
  List.existsb (fun '(s, _) => N.eqb slot s) active.

(* The declared value type of slot i.  Slots [0, param_count) are the
   parameters and [param_count, n) the declared locals, so the vector is
   params ++ modfunc_locals; coalesce_func only ever drops a suffix of
   modfunc_locals, so a slot that survives keeps this type. *)
Definition slot_types (types : list function_type) (f : module_func) :
  list value_type :=
  match lookup_N types f.(modfunc_type) with
  | Some (Tf ps _) => ps ++ f.(modfunc_locals)
  | None           => f.(modfunc_locals)
  end.

(* A candidate slot must be free *and* declared with the type we need.
   Without the type test an i64 local can be renamed onto a slot declared
   i32, and the resulting module fails validation -- so it cannot be
   instantiated, let alone run. *)
Definition slot_type_ok (tys : list value_type) (t : value_type) (slot : N) :
  bool :=
  match lookup_N tys slot with
  | Some t' => value_type_eqb t t'
  | None    => false
  end.

(* Returns `fallback` when no suitable slot exists.  Callers pass the local's
   own index, which is always in range and trivially of the right type, so an
   exhausted search degrades to "do not coalesce this local" rather than to a
   wrong or out-of-range slot. *)
Fixpoint find_free_slot_aux (tys : list value_type) (t : value_type)
  (active : list (N * nat)) (fallback : N)
  (remaining : nat) (slot : nat) : N :=
  match remaining with
  | O   => fallback
  | S r =>
    if slot_used_by_active (N.of_nat slot) active
       || negb (slot_type_ok tys t (N.of_nat slot)) then
      find_free_slot_aux tys t active fallback r (S slot)
    else N.of_nat slot
  end.

Definition find_free_slot (tys : list value_type) (param_count n : N)
  (idx : localidx) (active : list (N * nat)) : N :=
  match lookup_N tys idx with
  | Some t => find_free_slot_aux tys t active idx
                (N.to_nat (n - param_count)%N) (N.to_nat param_count)
  | None   => idx          (* unknown type: leave the local alone *)
  end.

Definition expire_active (def_pos : nat) (active : list (N * nat)) :
  list (N * nat) :=
  List.filter (fun '(_, l) => Nat.leb def_pos l) active.

Fixpoint linear_scan_loop
  (tys : list value_type)
  (param_count n : N)
  (intervals : list (localidx * nat * nat))
  (active : list (N * nat))
  (phi : local_map) {struct intervals} : local_map :=
  match intervals with
  | [] => phi
  | (idx, def_pos, last_use_pos) :: rest =>
    let active' := expire_active def_pos active in
    let slot := find_free_slot tys param_count n idx active' in
    let phi' := M.add idx slot phi in
    linear_scan_loop tys param_count n rest
      ((slot, last_use_pos) :: active') phi'
  end.

Definition linear_scan (tys : list value_type) (param_count n : N)
  (intervals : list (localidx * nat * nat)) : local_map :=
  linear_scan_loop tys param_count n
    (sort_by_def intervals) [] empty.

Definition compute_phi (tys : list value_type) (param_count n : N)
  (body : list basic_instruction) : local_map :=
  let st := walk_func param_count n body in
  if st.(ws_ok) then
    linear_scan tys param_count n (extract_intervals st)
  else empty.

(* ── Dropping the slots the rename no longer reaches ───────────────
   The scan packs the locals into the low slots, so the high ones come
   out unmentioned and their declarations can go.  What bounds the
   truncation is not the slots the scan *assigned* but the whole image
   of phi over the declared range: a local the body never mentions at
   all is absent from ws_defs, hence unassigned, hence left at its own
   index by apply_phi_local, and dropping its declaration would leave a
   frame too short for it.

   That is a real restriction rather than a conservatism the proof
   forces: [frames_agree] carries "every source index in range has its
   slot in range" universally, not just for the indices the code
   mentions, and a fresh activation has to satisfy it.  So one
   never-mentioned local declared last pins the count at n.  Every
   local CertiRocq emits is mentioned, and a local *read* without being
   written makes the walk reject the function outright, so the case
   that costs anything is a local declared and then used nowhere.

   [slot_bound_aux] is [N.max] over [apply_phi_local phi k] for k in
   [k, k + len), one past the largest, and [slot_bound] floors that at
   pc so the parameters are always kept.  On a rejected function phi is
   empty and the max is n, which is why the truncation degrades to
   "keep everything" without a special case. *)

Fixpoint slot_bound_aux (phi : local_map) (k : N) (len : nat) : N :=
  match len with
  | O   => 0%N
  | S l => N.max (N.succ (apply_phi_local phi k))
                 (slot_bound_aux phi (N.succ k) l)
  end.

Definition slot_bound (param_count n : N) (phi : local_map) : N :=
  N.max param_count
        (slot_bound_aux phi param_count (N.to_nat n - N.to_nat param_count)).

(* ── M3: coalesce_func / coalesce_module ───────────────────────── *)

(* The rename and the truncation share one [compute_phi]: it walks the
   whole body, and the extracted code would otherwise run it twice. *)
Definition coalesce_func (tys : list value_type) (param_count n : N)
  (f : module_func) : module_func :=
  let phi := compute_phi tys param_count n f.(modfunc_body) in
  {| modfunc_type   := f.(modfunc_type);
     modfunc_locals := List.firstn
                         (N.to_nat (slot_bound param_count n phi - param_count))
                         f.(modfunc_locals);
     modfunc_body   := List.map (apply_phi phi) f.(modfunc_body) |}.

Definition func_param_count (types : list function_type)
  (ti : typeidx) : N :=
  match lookup_N types ti with
  | Some (Tf ps _) => N.of_nat (length ps)
  | _              => 0%N
  end.

Definition func_total_locals (types : list function_type)
  (f : module_func) : N :=
  (func_param_count types f.(modfunc_type)
    + N.of_nat (length f.(modfunc_locals)))%N.

Definition coalesce_func_with_types (types : list function_type)
  (f : module_func) : module_func :=
  let pc  := func_param_count types f.(modfunc_type) in
  let n   := func_total_locals types f in
  let tys := slot_types types f in
  coalesce_func tys pc n f.

(* ── Supported input ───────────────────────────────────────────────
   Two restrictions on the module as a whole, checked rather than assumed,
   so that the correctness statement stays unconditional: an unsupported
   module is returned unchanged, and identity needs no proof.

   Both hold of every binary CertiCoq-Wasm produces today.

   1. Every slot is i32.  This is what makes the allocator's fallback
      safe.  find_free_slot returns the local's own index when its search
      is exhausted, and that index may already be held by a live local, so
      the fallback is unsound unless the search cannot be exhausted.  With
      a single type the count is immediate -- k live locals block k slots
      out of the n - param_count available, and the local being defined is
      not among them -- whereas with mixed types it needs a per-type
      argument.  It is also what makes the rename preserve validation:
      any slot has the type any local needs.

   2. No start section.  instantiate returns the initialisation code for
      the caller to run rather than running it, and get_init_expr_start
      makes that code end in [BI_call n] -- so with a start function the
      caller executes coalesced code during initialisation, and the
      correctness statement would have to cover that run too.  Without
      one, the initialisation code contains no call at all. *)

Definition slot_i32 (t : value_type) : bool := value_type_eqb t (T_num T_i32).

(* Two checks, both needed by the proof rather than by the pass.  The
   type check makes the free-slot search type-blind, hence a pure
   counting argument.  The guard is what lets the simulation relate a
   *rejected* function's body to itself: the pass leaves such a body
   alone, but rel_b still has to relate it, and its block, loop and if
   constructors all carry body_ok. *)
Definition func_supported (types : list function_type) (f : module_func) : bool :=
  List.forallb slot_i32 (slot_types types f)
  && bs_guarded f.(modfunc_body).

Definition module_supported (m : module) : bool :=
  match m.(mod_start) with
  | Some _ => false
  | None   => List.forallb (func_supported m.(mod_types)) m.(mod_funcs)
  end.

Definition coalesce_module_supported (m : module) : module :=
  let types := m.(mod_types) in
  {| mod_types   := m.(mod_types);
     mod_funcs   := List.map (coalesce_func_with_types types) m.(mod_funcs);
     mod_tables  := m.(mod_tables);
     mod_mems    := m.(mod_mems);
     mod_globals := m.(mod_globals);
     mod_elems   := m.(mod_elems);
     mod_datas   := m.(mod_datas);
     mod_start   := m.(mod_start);
     mod_imports  := m.(mod_imports);
     mod_exports  := m.(mod_exports) |}.

(* An unsupported module comes back untouched, so the correctness
   statement for it is reflexivity rather than a simulation. *)
Definition coalesce_module (m : module) : module :=
  if module_supported m then coalesce_module_supported m else m.
