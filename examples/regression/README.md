# Regression cases for the coalescing guard

Each `.wat` here is a minimal function that the pass must not miscompile.
`just regress` runs the pass over every one and checks that the output
validates; `branch` and `ssa` additionally have their behaviour compared
against the original under node.

| case     | what it exercises                                  | outcome |
|----------|----------------------------------------------------|---------|
| `ssa`    | two locals, same type, disjoint live ranges        | coalesced |
| `nonssa` | a local written twice                              | coalesced: the second write extends the first interval, it does not open a new one |
| `loop`   | a local defined inside a `loop` body               | accepted, nothing coalesced |
| `branch` | a local defined in one `if` branch, read after it  | accepted, nothing coalesced (the two locals are renamed but not merged) |
| `types`  | an `i32` and an `i64` local with disjoint ranges    | module rejected: the pass only accepts all-`i32` locals |

`branch` and `types` were both real miscompilations:

- `branch` produced a module that returned `42` instead of `0` when the `if`
  was not taken, because the shared slot still held the other local's value.
  The def of `local2` sits under an `if`, so it neither dominates its use
  after the `if` nor runs at most once — the two properties the interval
  model needs. It is now handled by giving a def at structured-control
  nesting depth > 0 an interval that starts at position 0: such a local
  interferes with everything, so it can never share a slot.
- `types` renamed an `i64` local onto a slot declared `i32`, producing a
  module that fails validation ("type mismatch: expected i32, found i64") and
  so cannot be instantiated at all. Slot selection is type-aware, and on top
  of that `module_supported` now refuses any module with a non-`i32` local,
  which is what rejects this case today.

`loop` and `branch` are the cost of the depth-0 pin: both are accepted and
both coalesce nothing, because every def they contain is guarded and so
interferes with every other local. Restricting the pin to locals that are
touched outside the construct guarding their def would recover most of that
— worth roughly 2772 -> 3979 slots saved on `examples/sha.wasm` in a model
of the change — but it is a second interval model and is not implemented.

## arms

A local written in one arm of an `if` and read in the other.  The read
happens on a path where the write never ran, so the local is *not* dead
outside its arm and its interval must open at function entry.  A walk
that judges "dead outside" from the instructions textually following the
arm misses the sibling and coalesces the local onto a dead one's slot;
`f(0)` then returns 42 instead of 0.
