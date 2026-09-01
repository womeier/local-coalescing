# Proof status — confined intervals

State of branch `confined-loop`, at commit `a613718`. `dune build` is green.

## What changed in the pass

A def under structured control used to open its interval at 0
unconditionally. It now opens at its own position when the local is dead
outside the body, and at 0 otherwise. "Outside" is meant in the control
sense, so `ws_self` carries whole enclosing lists rather than the parts
still to run — `examples/regression/arms.wat` is the case that forced
this, and it miscompiled under the suffix version while every existing
test passed.

The important consequence for the proof: a local read *inside* a body is
still read on the stack (`stack_read` / `bs_live_b` recurse into the
body through `bi_live`), so a first def of it under structured control
opens at 0. A def opens at its own position only for a local played
nowhere in the enclosing lists, and such a local never appears in the
relation's live sets. The anchors therefore behave like before.

On `examples/sha.wasm`: declared locals 4379 → 400, against binaryen's
203. The largest function goes 101 → 7, binaryen 6.

## What changed in the proof

All five helper admits (`kill_recorded`, `defs_none_walk`, `encl_ok_cons`,
`seen_of_encl`, `stack_ok_enter`) and `walk_live_start` are proved
(`72fb63d`), together with the machinery replacing the deleted
`defs_le` / `walk_inv_nonzero`: `walk_inv_seen` (defs stay under P while
the stack reads the local), `walk_instr_inv_seen` (a def of a local the
walk is inside is never found past P; the seen condition is only
consulted for structured instructions), `stack_ok_step`,
`K_anchored_mono` (`6eb9ac3`). `rel_bs_of_walk`'s statement carries the
`d = 0` guard on its size bound (`a613718`), so a structured body is
recursed with `E` anchored at its own level start; `coalesce_func_related`
is adapted. `rel_bs_agnostic` (`c40fdf7`): a write-free `rel_bs` is inert
in its live set.

## Admitted (1, theories/alloc_correct.v)

| lemma | note |
|-------|------|
| `rel_bs_of_walk` | the only one the top depends on |

## The loop case

Not blocked. A loop body written under this pass has its body-relevant
first defs opening at 0 (the enclosing list's liveness recurses into the
body), so the strong `relb_loop` body — related under
`bs_live_b bs \/ K` — is reachable: the defs overlap every write, and
`slot_free` holds. The remaining work is the ordinary proof, which the
`walk_instr_inv_seen` / `walk_inv_seen` / anchor machinery is set up for.