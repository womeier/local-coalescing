# Plan — Local coalescing pass

A function-local coalescing pass over the WasmCert AST: merge **declared
locals** with non-overlapping live ranges into shared slots via a rename map
`phi : localidx -> localidx`, applied to `local.get`/`local.set`/`local.tee`.
Wire it into parse -> coalesce -> print, extract to OCaml, and validate by
round-trip on `examples/foo.wasm` and `examples/sha.wasm`.

**This round = implement + test only. No `Theorem`/`Proof`.** The eventual
proof goal (backward simulation) is recorded below and is *out of scope* for
this round; design choices are made to keep it tractable later.

**Parameters are kept as-is** (`phi(p) = p`); only declared locals are renamed.
See §3.

---

## 1. Confirmed decisions

1. **Semantics of coalescing**: merge locals with non-overlapping live ranges;
   `phi` renames each original declared local to its coalesced slot.
2. **Deliverable this round**: interval collection + linear scan + `apply_phi`
   (the transformation). No proofs; test first.
3. **Control-flow scope**: function-local, recursing into nested
   `BI_block`/`BI_loop`/`BI_if`.
4. **Local count**: rename only; `modfunc_locals` unchanged (count-preserving;
   real slot-count reduction deferred).
5. **Parameters**: kept as-is — `phi(p) = p`, excluded from coalescing, no
   intervals computed for them. Only declared locals are changed.
6. **`BI_local_tee`**: ≡ `BI_local_set` for live-range purposes (the get-half
   reads the just-stored value); `apply_phi` renames its index. Absent in the
   test binaries; handled for completeness.
7. **Correctness proof**: deferred (this round = executable pass + empirical
   test).
8. **Existing file**: clean up `theories/coalesce_locals.v` (remove
   `Admit Obligations`, dead commented `ir` IR, the duplicate `validate_instrs`,
   the dangling `Print`); keep `local_map`/`empty`/notations; continue in it.
   Add `coalesce_locals` to `theories/dune`.
9. **Pipeline / extraction**: insert coalesce between parse and print; extract
   the new entry point; update `src/main.ml`.
10. **No graph coloring this round**: the target binaries are in an SSA-like
    fragment where each local is written exactly once, so live ranges are
    single intervals and coalescing reduces to **linear scan** (Poletto &
    Sarkar, PLDI 1999) — no interference graph, no graph-coloring algorithm.

---

## 2. Supported fragment (calibrated from foo.wasm / sha.wasm)

Disassembly of both binaries shows the local-touching / control instructions
are exactly `local.get`, `local.set`, `if`/`else`, `return`. There are
**zero** `loop`, `block`, `br`, `br_if`, `br_table`, `local.tee` in either
binary. This matches the "linear control flow, no local ops in loops"
constraint.

`coalescable_func` (conservative v1) — return `false` (skip -> return the
function unchanged) if any of:

- the body contains `BI_br`, `BI_br_if`, `BI_br_table`, or `BI_loop`;
- some declared local is written (`local.set`/`local.tee`) more than once
  (violates the single-write assumption the linear scan relies on);
- some declared local is read (`local.get`) before its write in source order
  (a pre-def use; would read zero and breaks the interval model).

Functions using only `if`/`return` + straight-line code, with single-write
locals, are accepted (all of foo/sha qualify). `BI_block` is allowed and
recursed linearly. `BI_return` needs no special handling for interval
collection (see §3). Relaxable later.

### Soundness caveat (and why the test is the safety net)

Linear scan on source-order intervals is sound **iff** each local's live range
is a single contiguous interval. This holds under single-write +
def-dominates-uses **in the CFG sense** (the def's branch dominates all uses,
i.e. a local defined inside an `if` is used only within that same branch). The
v1 guard checks the cheaper source-order approximation (def precedes use); the
full CFG-dominance / scope-balanced check is the documented escalation if the
round-trip test fails (see §10 fallback). Concretely, the failure mode is a
local defined in one `if`-branch and read after the merge on a path where it
wasn't defined — the test (`just foo`/`just sha` + `compare_output.py`)
catches this empirically.

---

## 3. Interval collection — single forward walk

One forward traversal of the instruction tree in source order (recursing into
`BI_if`/`BI_block`/`BI_loop`, flattening branches in source order), assigning
each instruction a position. Per **declared** local `[param_count, n)`,
record:

- `def_pos(i)` — position of its single `BI_local_set`/`BI_local_tee`;
- `last_use_pos(i)` — position of its last `BI_local_get` (or `def_pos` if
  never read).

Validate the §2 guards on the fly:

- `BI_local_set`/`tee i` with `i` already defined -> second write -> skip;
- `BI_local.get i` with `i` not yet defined -> pre-def use -> skip.

`BI_return` / `BI_if` / `BI_block` / `BI_loop`: just recurse (positions
continue in source order); no special liveness handling — the source-order
span is intended as a sound over-approximation under the §2 caveat.

### Parameters (kept as-is)

Param indices `[0, param_count)` — `param_count` from resolving
`modfunc_type` (a `typeidx`) against the module's `mod_types` to get the
`function_type` and its parameter arity — are **fixed**: `phi(p) = p`, no
intervals computed, excluded from coalescing. They occupy slots
`[0, param_count)`; declared locals are coalesced into `[param_count, n)`.
The two slot ranges are disjoint, so no cross-interference tracking is needed.
Total `n = param_count + length(modfunc_locals)`.

---

## 4. Linear scan -> `phi` (exposed)

Linear scan (Poletto & Sarkar) over the collected intervals
`[def_pos(i), last_use_pos(i)]`:

- Sort intervals by `def_pos` (ascending).
- Maintain `active` = intervals started but not ended, keyed by `last_use_pos`.
- For each interval `i` in def order:
  - expire from `active` any interval whose `last_use_pos < def_pos(i)` (free
    its slot);
  - assign `slot(i)` = smallest free slot in `[param_count, n)` not used by
    `active`;
  - add `i` to `active`.

`phi(i) = slot(i)` for declared locals; `phi(p) = p` for params; identity for
unreferenced locals. Stored as `local_map` (AVL, `localidx -> localidx`),
defaulting to identity.

**Proof-readiness tweak**: expose `phi` as a first-class, inspectable output
of `coalesce_func` (e.g. a record `{ cofunc_phi : local_map;
cofunc_func : module_func }`, or a separate `compute_phi` that `coalesce_func`
calls). The eventual simulation relation `R_phi` references `phi`, so it must
be nameable.

---

## 5. `apply_phi` (transformation)

`apply_phi : local_map -> basic_instruction -> basic_instruction`, lifted over
lists and recursing into `BI_block`/`BI_loop`/`BI_if`:

- `BI_local_get i` -> `BI_local_get (phi i)`
- `BI_local_set i` -> `BI_local_set (phi i)`
- `BI_local_tee i` -> `BI_local_tee (phi i)`
- All else unchanged (recurse into sub-bodies).

Shape-preserving (identical instruction count/structure); `modfunc_locals`
unchanged. Lookup of `phi` defaults to identity for indices not in the map
(params, unreferenced locals).

---

## 6. Drivers

- `coalesce_func : module_func -> module_func` — takes the param_count
  (resolved by the caller from `mod_types`) and applies the coalescing
  transformation. Internally: if `~ coalescable_func` -> identity.
  Else: forward walk (intervals + guard) -> linear scan -> `phi` (params
  fixed) -> `apply_phi phi` applied to `f.(modfunc_body)`.
  The phi map is computed internally and used for the transformation;
  it is not exposed in the return type. For the proof, `phi` can be
  extracted via a separate `compute_phi` helper or reconstructed.
- `coalesce_module : module -> module` — `mod_funcs` mapped by
  `coalesce_func`; everything else unchanged.

---

## 7. File / build changes

- `theories/coalesce_locals.v`: remove `Admit Obligations`, dead commented
  `ir` IR, the duplicate `validate_instrs`, the dangling `Print`. Repurpose
  into interval-collection forward walk + linear scan + `apply_phi` + drivers.
  Keep `local_map`/`empty`/notations. Prefer plain `Fixpoint` (structural
  recursion on the instruction tree) to avoid `Program`-measure obligations;
  where unavoidable, discharge the trivial termination obligation with
  `Defined`. The old `validate_instrs`/`uses_localidx` sketch is superseded
  (drop, or keep `uses_localidx` only if used as a helper).
- `theories/dune`: add `coalesce_locals` to `(modules ...)`.
- `theories/pipeline.v`: add `coalesce_module` between parse and print (new
  `optimize` entry; keep or replace `parse_and_print`).
- `src/extraction.v`: extract the new entry point.
- `src/main.ml`: call it.
- `justfile`: unchanged (`just foo` / `just sha` already run + compare).

---

## 8. Testing

1. `just build` — compiles cleanly, no admits.
2. `just foo` — `foo_opt.wasm` run via `foo.js`; passes iff behavior identical.
3. `just sha` / `just sha_check` — same for `sha.wasm` (~20s parse) +
   `compare_output.py`.

Since only non-interfering locals merge and the count is preserved, semantics
is preserved -> tests should pass. A failure means a mis-coalesce (most likely
a §2 soundness-caveat violation) -> add the scope-balanced / CFG-dominance
guard, or fall back to backward liveness + coloring (§10).

---

## 9. Eventual proof goal (deferred — out of scope this round)

A **backward simulation** (Compcert-style: simulate the *optimized* function
back to the *source*) whose corollary is the whole-call equivalence:

> For any context `C = (host_state, store, module_instance, args)`, calling
> `f` and calling `coalesce_func f` from `C` compute the same result.

### Correctness statement (scaffold)

The proof has two parts:

**Part A — Shape preservation** (`apply_phi` preserves instruction count):

```coq
Lemma apply_phi_preserves_bi_size : forall phi i,
  bi_size (apply_phi phi i) = bi_size i.
```

This follows by induction on `i`: `apply_phi` only renames local indices,
leaving instruction structure (including sub-blocks) unchanged.

**Part B — Backward simulation** (parameterized over host typeclass
instances via `Section Correctness` / `Context`):

```coq
Section Correctness.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory} `{ho : host}.

Theorem coalesce_func_correct : forall phi f,
  let f_body  := f.(modfunc_body) in
  let f_body' := List.map (apply_phi phi) f_body in
  forall hs hs' s s' f_src f_opt f_opt' es',
    f_inst f_src = f_inst f_opt ->
    R_phi phi (f_locs f_src) (f_locs f_opt) ->
    reduce hs s f_opt (List.map AI_basic f_body')
           hs' s' f_opt' es' ->
    exists f_src' es0,
      reduce hs s f_src (List.map AI_basic f_body)
             hs' s' f_src' es0 /\
      R_phi phi (f_locs f_src') (f_locs f_opt').
End Correctness.
```

The key invariant: `R_phi` holds at function entry (params line up via
`phi(p) = p`, declared locals are zero-init in both frames) and is
preserved through each reduction step (lockstep via `apply_phi`
shape-preservation + single-write dominance).

### Why the current design already makes this tractable

- **Keep `modfunc_locals` unchanged + params fixed** (`phi(p)=p`): at the call
  boundary, params line up directly and all declared locals are zero-init in
  *both* frames, so `locs[i] = locs'[phi i]` holds *trivially at function
  entry* — the initial correspondence is free.
- **`apply_phi` shape-preserving**: every original instruction has exactly
  one matching optimized instruction -> **lockstep** simulation, so the
  per-step match is structurally trivial (same `reduce` rule applies to both,
  reading/writing corresponding slots under `R_phi`).
- **Single-write + dominance**: each declared local is assigned exactly one
  slot and its value flows linearly, so `R_phi` is preserved through each
  instruction without re-establishing complex invariants.

---

## 10. Explicitly out of scope this round

- Any `Theorem`/`Proof` of correctness (syntactic validator theorem and the
  backward-simulation / `reduce` semantic preservation above).
- Shrinking `modfunc_locals` (real slot-count reduction).
- Handling `br`/`br_if`/`br_table`/`loop` bodies with local ops (skipped via
  `coalescable`).
- **General backward-liveness + interference-graph + graph-coloring** for
  functions outside the single-write / linear-control-flow fragment. This is
  the documented **fallback** if the round-trip test fails (i.e. if the
  source-order interval model turns out unsound for some function). Not
  needed for foo/sha unless tests reveal a problem.
- A standalone `validate_instrs` translation-validator (superseded for now by
  direct construction; can be re-added later as the certification front for
  an unverified `phi` producer).

---

## 11. Milestones

- **M1** forward interval-collection walk + single-write / source-dominance
  guard (compile).
- **M2** linear scan -> `phi` (params fixed, `phi` exposed) (compile).
- **M3** `apply_phi` + `coalesce_func` / `coalesce_module` (compile).
- **M4** wire pipeline + extraction; `just foo` passes.
- **M5** `just sha` passes.

---

## 12. Open items / flagged

- **WasmCert paper reference**: the README labels
  <https://inria.hal.science/inria-00529841/document> as the "WasmCert paper",
  but the link's identity is **unverified** — the fetch was blocked by an
  anti-bot (Anubis) page. Needs manual confirmation that it is indeed the
  WasmCert paper; if not, replace with the correct WasmCert-Coq paper URL.
- **Linear-scan soundness** depends on the §2 caveat (single-write +
  def-dominates-uses in the CFG sense). The v1 guard checks the cheaper
  source-order approximation; the round-trip test is the safety net, with the
  backward-liveness+coloring fallback (§10) if it fails.
