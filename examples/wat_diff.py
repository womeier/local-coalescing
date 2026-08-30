#!/usr/bin/env python3
"""Count the locals each function declares, before the pass and after,
against what binaryen's own coalescer manages on the same input.

    wat_diff.py before.wasm after.wasm

Writes <before>.wat, <after>.wat and <before>-binaryen.wat next to the
inputs and prints a per-function report of the declared-locals counts.

The count is the number of type entries on the function's `(local ...)`
line -- the i32s in `(local i32 i32 i32 i32 i32 i32)` -- and nothing
else.  Parameters are not counted: they are function inputs, not slots
the pass is free to reuse.

The `wasm-opt` column is `wasm-opt --coalesce-locals` run on the same
input, as the reference point for what this pass is trying to do.  It is
not a target to match: binaryen's pass rewrites the declaration vector,
and ours deliberately does not (`apply_phi_func` in
theories/coalesce_locals.v copies modfunc_locals through verbatim and
only renumbers the body), so the two columns are not measuring equal
work.  The column is here to show the size of the gap, and to move once
the pass starts truncating the vector.

Counting is done on the .wat rather than the binary because that is the
artifact a reader will actually open, so the numbers and the file they
are meant to describe cannot drift apart.  wasm-tools opens each defined
function with `(func (;N;) ...` and prints its declarations on the next
line as `(local i32 i32 ...)`, omitting that line entirely when there
are none.
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile

FUNC_LINE = re.compile(r"^\s*\(func\s+\(;(\d+);\)")
LOCAL_LINE = re.compile(r"^\s*\(local\s+([^)]*)\)\s*$")


def to_wat(wasm_path, wat_path):
    with open(wat_path, "w") as out:
        subprocess.run(["wasm-tools", "print", wasm_path], stdout=out, check=True)


def wasm_opt_wat(wasm_path, wat_path):
    """Run `wasm-opt --coalesce-locals` on wasm_path, print it to wat_path.

    Returns False if binaryen is not installed or refuses the input, so a
    missing reference degrades to a two-column report rather than taking
    the whole run down with it.

    --all-features because CertiCoq emits return_call_indirect, which
    wasm-opt rejects at validation unless tail calls are enabled.  The
    pass cannot introduce a feature the input did not already use, so
    turning them all on only affects what it agrees to read."""
    # A stale reference .wat from an earlier run would outlive the column
    # it belongs to and be read as current, so drop it on every bail-out.
    def skip(why):
        print(f"note: {why}, skipping the binaryen column", file=sys.stderr)
        if os.path.exists(wat_path):
            os.remove(wat_path)
        return False

    if shutil.which("wasm-opt") is None:
        return skip("wasm-opt not found")
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "coalesced.wasm")
        r = subprocess.run(
            ["wasm-opt", "--all-features", "--coalesce-locals", wasm_path,
             "-o", out],
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            first = r.stderr.strip().splitlines()[:1]
            return skip(f"wasm-opt failed: "
                        f"{first[0] if first else r.returncode}")
        to_wat(out, wat_path)
    return True


def locals_per_func(wat_path):
    """Map function index -> declared-locals count, for defined functions.

    A function that declares none prints no `(local ...)` line, and is
    recorded as 0 rather than skipped, so the columns of the report line
    up by function index even if a pass empties one out."""
    counts = {}
    current = None
    with open(wat_path) as f:
        for line in f:
            m = FUNC_LINE.match(line)
            if m:
                current = int(m.group(1))
                counts[current] = 0
                continue
            m = LOCAL_LINE.match(line)
            if m and current is not None:
                counts[current] = len(m.group(1).split())
    return counts


def main(argv):
    if len(argv) != 3:
        print(f"usage: {argv[0]} before.wasm after.wasm", file=sys.stderr)
        return 2
    before, after = argv[1], argv[2]
    stem = before.removesuffix(".wasm")
    before_wat = stem + ".wat"
    after_wat = after.removesuffix(".wasm") + ".wat"
    ref_wat = stem + "-binaryen.wat"

    to_wat(before, before_wat)
    to_wat(after, after_wat)
    have_ref = wasm_opt_wat(before, ref_wat)

    b = locals_per_func(before_wat)
    a = locals_per_func(after_wat)
    r = locals_per_func(ref_wat) if have_ref else {}
    if a.keys() != b.keys():
        print("WARNING: the two modules define different functions -- "
              "the pass should not add or remove any", file=sys.stderr)

    cols = f"{'func':>6}  {'before':>8}  {'ours':>8}"
    if have_ref:
        cols += f"  {'binaryen':>8}"
    # measured off the header rather than counted by hand, so the rule
    # cannot drift from the columns when one is added or dropped
    width = len(cols)
    print(cols)
    print("-" * width)
    unchanged = 0
    for i in sorted(b):
        x, y, z = b[i], a.get(i, 0), r.get(i, 0)
        if x == y and (not have_ref or x == z):
            unchanged += 1
            continue
        row = f"{i:>6}  {x:>8}  {y:>8}"
        if have_ref:
            row += f"  {z:>8}"
        print(row)
    print("-" * width)

    tb, ta, tr = sum(b.values()), sum(a.values()), sum(r.values())
    total = f"{'total':>6}  {tb:>8}  {ta:>8}"
    saved = f"{'saved':>6}  {'':>8}  {tb - ta:>8}"
    if have_ref:
        total += f"  {tr:>8}"
        saved += f"  {tb - tr:>8}"
    print(total)
    print(saved)

    def pct(t):
        return f"{100 * (tb - t) / tb:.1f}%" if tb else "n/a"
    print()
    print(f"ours:     {pct(ta)} of declared locals, "
          f"{unchanged} of {len(b)} functions unchanged")
    if have_ref:
        print(f"binaryen: {pct(tr)} of declared locals")
    print()
    print(f"wat:  {before_wat}")
    print(f"      {after_wat}")
    if have_ref:
        print(f"      {ref_wat}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
