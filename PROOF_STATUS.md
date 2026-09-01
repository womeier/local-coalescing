# Proof status — confined intervals

State of the branch `confined-loop`, at commit `a613718` (all PROOF_STATUS
admits except `rel_bs_of_walk` are closed; `dune build` is green).

## What changed in the pass

A def under structured control used to open its interval at 0
unconditionally. It now opens at its own position when the local is dead
outside the body, and at 0 otherwise. "Outside" is meant in the control
sense, so `ws_self` carries whole enclosing lists rather than the parts
still to run — `examples/regression/arms.wat` is the case that forced
this, and it miscompiled under the suffix version while every existing
test passed.

On `examples/sha.wasm`: declared locals 4379 → 400, against binaryen's
203. The largest function goes 101 → 7, binaryen 6.

## What changed in the proof

All five helper admits (`kill_recorded`, `defs_none_walk`, `encl_ok_cons`,
`seen_of_encl`, `stack_ok_enter`) and `walk_live_start` are proved
(`72fb63d`), together with the machinery that replaced the deleted
`defs_le` / `walk_inv_nonzero`: `walk_inv_seen` (defs stay under P while
the stack reads the local), `walk_instr_inv_seen` (a def of a local the
walk is inside is never found past P — the seen condition is only
consulted for structured instructions), `stack_ok_step`,
`K_anchored_mono` (`6eb9ac3`).

`rel_bs_of_walk`'s statement was restored to carry the `d = 0` guard on
its size bound (`a613718`), so a structured body can anchor `E` at its
own level start instead of being pinned to one `E` for the whole descent;
`coalesce_func_related` is adapted.

## Admitted (1, theories/alloc_correct.v)

| line | lemma | note |
|------|-------|------|
| 1933 | `rel_bs_of_walk` | the only one the top depends on |

## The open loop case — a statement gap, not a proof gap

`relb_loop` (in coalesce_locals_correct.v) requires a loop body to relate
under `bs_live_b bs \/ K`. Under the new confinement this is **false of
the pass's own output** for some loop bodies, and the failure is a real
counterexample, not a missing lemma:

    loop
      local.get j    drop      (* j read early, never again *)
      local.set i              (* i's write: j is dead, interval disjoint *)
    end

Both locals are merged into slot 0 (their intervals do not overlap, so
the scan reuses a slot; shadow.wat is the flat version of the same
pattern). At `local.set i` the continuation is required to be
`slot_free phi (bs_live_ext tail (bs_live bs \/ K)) i`, which includes j
(`bs_live_b j bs`, not killed in the tail), but `phi j = phi i = 0`, so
the relation under `bs_live_b bs \/ K` fails. Every strategy that keeps
`relb_loop` strong therefore cannot build a `rel_bs` for the loop body
from the walk, and every strategy that weakens `relb_loop` to plain `K`
(the PROOF_STATUS "agreed direction") cannot build the `r_loop` label
step's body relation, which `rel_label` fixes to the same
`bs_live \/ K` set. Both were tested interactively; the exact failing
goals are recorded below.

### Strategies attempted

1. **Weaken `relb_loop` to plain `K`** — verified interactively. The
   `r_loop` corresp step then has `Hbs : rel_bs phi K es bs_o` and must
   build `rel_es phi (es_live_b [loop] \/ K) ...`, whose residual

       forall i, es_live_b i [AI_basic (BI_loop tb es)] \/ live_ext [] K i
              -> live_ext [] K i

   is unprovable: `es_live_b i [loop] = bs_live_b i es` is not implied by
   `live_ext [] K i`. The write-free half of `body_ok` closes with
   `rel_bs_agnostic` (committed `c40fdf7`: a write-free `rel_bs` is inert
   in its live set); the branch-free half — a *writing* body — provably
   cannot because `slot_free` in the over-approximated set fails for a
   local read before a middle write whose slot the pass reuses.

2. **Strong `relb_loop`, walk builds the body under `bs_live_b bs \/ K`**
   — the body recursion needs `K_anchored ... E (bs_live_b bs \/ K)`,
   i.e. `dj <= ws_pos st` for a first def in the body, but the confinement
   rule opens such a def at its *own* position (the body is not on the
   walk's stack), which is after `ws_pos st`. Underivable.

### Where this leaves the proof

`rel_bs_of_walk`'s cons / block / if cases are fully scaffolded
(`walk_instr_inv_seen`, `stack_ok_step`, `K_anchored_mono`, the `d = 0`
guard). The loop case needs a *semantic* decision about how a writing
`loop` body is represented in the relation after it is merged — either
the pass must not merge a loop body whose first defs sit late (keeping
`relb_loop` strong only where the intervals reach the anchor), or the
`r_loop` label step must relate a branch-free body under the plain
continuation instead of the label's own live set. Both touch
`coalesce_locals_correct.v` and/or `coalesce_locals.v` and are outside
the walk-to-relation proof proper.