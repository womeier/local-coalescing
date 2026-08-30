#!/usr/bin/env python3
"""Print two binaries as .wat, diff them, and summarise the locals saved.

    wat_diff.py before.wasm after.wasm

Writes <before>.wat, <after>.wat and <before>.wat.diff next to the inputs
and prints a per-function report of the declared-locals counts.

The diff itself is not printed: for examples/sha.wasm it runs to some
47k lines, which is unreadable in a CI log.  It is left on disk for the
workflow to upload as an artifact, and only the summary goes to stdout.

Counting is done on the .wat rather than the binary because that is the
artifact a reader will actually open, so the numbers and the file they
are meant to describe cannot drift apart.  wasm-tools opens each defined
function with `(func (;N;) ...` and prints its declarations on the next
line as `(local i32 i32 ...)`, omitting that line entirely when there
are none.
"""

import re
import subprocess
import sys

FUNC_LINE = re.compile(r"^\s*\(func\s+\(;(\d+);\)")
LOCAL_LINE = re.compile(r"^\s*\(local\s+([^)]*)\)\s*$")


def to_wat(wasm_path, wat_path):
    with open(wat_path, "w") as out:
        subprocess.run(["wasm-tools", "print", wasm_path], stdout=out, check=True)


def locals_per_func(wat_path):
    """Map function index -> declared-locals count, for defined functions.

    A function that declares none prints no `(local ...)` line, and is
    recorded as 0 rather than skipped, so the two sides of the report
    line up by function index even if the pass empties one out."""
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
    before_wat = before.removesuffix(".wasm") + ".wat"
    after_wat = after.removesuffix(".wasm") + ".wat"
    diff_path = before_wat + ".diff"

    to_wat(before, before_wat)
    to_wat(after, after_wat)

    with open(diff_path, "w") as out:
        # diff exits 1 when the files differ, which is the expected case
        subprocess.run(["diff", "-u", before_wat, after_wat], stdout=out)
    diff_lines = sum(1 for _ in open(diff_path))

    b = locals_per_func(before_wat)
    a = locals_per_func(after_wat)
    if a.keys() != b.keys():
        print("WARNING: the two modules define different functions -- "
              "the pass should not add or remove any", file=sys.stderr)

    print(f"{'func':>6}  {'before':>8}  {'after':>8}  {'saved':>8}")
    print("-" * 38)
    unchanged = 0
    for i in sorted(b):
        x, y = b[i], a.get(i, 0)
        if x == y:
            unchanged += 1
            continue
        print(f"{i:>6}  {x:>8}  {y:>8}  {x - y:>8}")
    print("-" * 38)
    tb, ta = sum(b.values()), sum(a.values())
    pct = f"{100 * (tb - ta) / tb:.1f}%" if tb else "n/a"
    print(f"{'total':>6}  {tb:>8}  {ta:>8}  {tb - ta:>8}  ({pct} of declared locals)")
    print(f"{unchanged} of {len(b)} functions unchanged")
    print()
    print(f"wat:  {before_wat}")
    print(f"      {after_wat}")
    print(f"diff: {diff_path} ({diff_lines} lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
