#!/usr/bin/env python3
"""Find, and optionally delete, lemmas nothing in the development depends on.

Run via `just unused` (report) or `just prune` (delete).  Must run from the
repository root, against an up-to-date _build.

HOW IT DECIDES
--------------
dpdgraph's `Print FileDependGraph` writes the call graph of the whole theory,
and `dpdusage` reports every proof in it with no incoming edge.  Raw dpdusage
output is unusable on its own -- most of it is the FMapAVL functor instance
inside coalesce_locals (M.Raw.*) plus Rocq's generated _ind/_rec/_sind schemes
-- so we keep only names a theories/*.v file declares with a Lemma/Theorem/...,
minus the roots below.

What survives is split in two.  dpdgraph reads proof terms, so it cannot see a
name used from an Ltac body, a hint, or a comment: es_neutral_cat has no proof
depending on it, but neutral_solve still applies it, and deleting it breaks the
build.  A name occurring more than once across theories/*.v has such a mention
besides its own declaration, and is reported separately as needing a look.  The
rest is unreferenced by anything at all, and is what --prune deletes.

WHAT IT DELETES
---------------
The declaration line through the Qed./Defined./Admitted. that closes it, plus a
comment block sitting directly on top, which in this development always belongs
to the lemma below it.  The declaration is checked against the expected name
first, so nothing is removed on a mismatch.

Only the seam a deletion leaves is tidied: blank against blank collapses to one
blank.  The rest of the file is left byte for byte alone, so the diff is
exactly the lemmas and nothing else.

Deleting cascades -- a lemma whose only users were themselves dead becomes
visible only once they are gone -- so --prune re-scans and repeats, rebuilding
between rounds and stopping on the first build failure.  `git checkout
theories/` undoes the lot.

Comments are the one thing this cannot get right on its own: a deleted lemma
named in surrounding prose leaves the prose stale.  Read the diff.
"""

import argparse
import glob
import os
import re
import subprocess
import sys
import tempfile

# coalesce_module_correct is the main correctness theorem -- the thing the whole
# development exists to prove, and what `just print_assumptions` checks; the
# other two are what src/extraction.v extracts.  None of them has, or should
# have, a user inside the development.  Never report these.
ROOTS = {"coalesce_module_correct", "parse_and_print", "parse_optimize_print"}

THEORIES = "theories"
DECL = re.compile(
    r"^\s*(?:Lemma|Theorem|Corollary|Remark|Fact|Proposition|Property|Example)"
    r"\s+([A-Za-z0-9_']+)\b"
)
END = re.compile(r"(?:Qed|Defined|Admitted)\.\s*$")


def sources():
    return sorted(glob.glob(os.path.join(THEORIES, "*.v")))


def build_graph(dpd):
    """Ask Rocq for the dependency graph of every module under theories/.

    `rocq repl`, not `dune rocq top`: dune builds the load path from
    theories/dune, which does not list dpdgraph, whereas rocq repl finds it on
    the ROCQPATH the nix shell already sets.
    """
    mods = " ".join(os.path.basename(f)[:-2] for f in sources())
    script = (
        "Require dpdgraph.dpdgraph.\n"
        f"From Wasmopt Require {mods}.\n"
        f'Set DependGraph File "{dpd}".\n'
        f"Print FileDependGraph {mods}.\n"
    )
    proc = subprocess.run(
        ["rocq", "repl", "-R", "_build/default/theories", "Wasmopt"],
        input=script,
        capture_output=True,
        text=True,
    )
    if not os.path.exists(dpd):
        noise = re.compile(r"^(\[Loading|Fetching|Welcome|Rocq <|$)")
        for line in (proc.stdout + proc.stderr).splitlines():
            if not noise.match(line):
                print(line, file=sys.stderr)
        raise SystemExit("could not build the dependency graph")


def unused_names(dpd):
    """Names dpdusage reports with no incoming edge, module prefix stripped."""
    out = subprocess.run(
        ["dpdusage", dpd], capture_output=True, text=True, check=True
    ).stdout
    names = set()
    for line in out.splitlines():
        # "coalesce_locals.M.Raw.Proofs:gt_left\t(0)"
        name = line.split("\t")[0].rsplit(":", 1)[-1]
        if name and not name.startswith("Info:"):
            names.add(name)
    return names - ROOTS


def declarations():
    """name -> "file:line" for everything theories/*.v declares as a lemma."""
    found = {}
    for path in sources():
        for n, line in enumerate(open(path), start=1):
            m = DECL.match(line)
            if m:
                found[m.group(1)] = f"{path}:{n}"
    return found


def mention_counts(names):
    """How often each name occurs across theories/*.v, its declaration included.

    Rocq identifiers may end in a quote, which \\b mishandles, so the boundary
    is spelled out.
    """
    text = "\n".join(open(p).read() for p in sources())
    return {
        name: len(
            re.findall(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])", text)
        )
        for name in names
    }


def scan():
    """(dead, mentioned), each a sorted list of (name, "file:line")."""
    with tempfile.TemporaryDirectory() as tmp:
        dpd = os.path.join(tmp, "wasmopt.dpd")
        build_graph(dpd)
        candidates = unused_names(dpd)

    declared = declarations()
    candidates &= declared.keys()
    counts = mention_counts(candidates)

    dead, mentioned = [], []
    for name in sorted(candidates):
        entry = (name, declared[name])
        (mentioned if counts[name] > 1 else dead).append(entry)
    return dead, mentioned


def show(entries, title=None):
    if title:
        print(title)
    for name, loc in entries:
        print(f"  {name:<42} {loc}")


def report():
    dead, mentioned = scan()
    print()
    if dead:
        show(dead, f"unused lemmas ({len(dead)}) -- nothing refers to these at all:")
    else:
        print("no unused lemmas")
    if mentioned:
        print()
        print(f"no proof depends on these ({len(mentioned)}), but the name still")
        print("occurs in theories/ -- an Ltac alternative, a hint, or a comment:")
        show(mentioned)


def block(lines, index, name):
    """The half-open line range holding name's comment, declaration and proof."""
    m = DECL.match(lines[index])
    if not m or m.group(1) != name:
        raise SystemExit(
            f"expected a declaration of {name} at line {index + 1}, found:\n"
            f"  {lines[index].rstrip()}"
        )

    end = index
    while not END.search(lines[end]):
        end += 1
        if end >= len(lines):
            raise SystemExit(f"{name}: no Qed./Defined./Admitted. before end of file")

    start = index
    if start > 0 and lines[start - 1].rstrip().endswith("*)"):
        c = start - 1
        while c >= 0 and not lines[c].lstrip().startswith("(*"):
            c -= 1
        if c >= 0:
            start = c

    return start, end + 1


def cut(path, items, dry_run):
    """Remove `items`, a list of (line, name), from one file.  Returns lines cut."""
    lines = open(path).read().split("\n")
    doomed = set()
    for line_no, name in sorted(items, reverse=True):
        start, end = block(lines, line_no - 1, name)
        if dry_run:
            print(f"    {name:<42} {path}:{start + 1}-{end} ({end - start} lines)")
        doomed.update(range(start, end))
    if dry_run:
        return len(doomed)

    kept = []
    for n, line in enumerate(lines):
        if n in doomed:
            continue
        # blank against blank, and the gap between them is what we just removed
        if line.strip() == "" and kept and kept[-1].strip() == "" and n - 1 in doomed:
            continue
        kept.append(line)
    open(path, "w").write("\n".join(kept))
    return len(doomed)


def prune(dry_run, max_rounds=10):
    for round_no in range(1, max_rounds + 1):
        dead, _ = scan()
        if not dead:
            print(f"round {round_no}: nothing left to remove")
            return
        print(f"round {round_no}: {len(dead)} lemmas")

        by_file = {}
        for name, loc in dead:
            path, line_no = loc.rsplit(":", 1)
            by_file.setdefault(path, []).append((int(line_no), name))

        total = 0
        for path, items in sorted(by_file.items()):
            total += cut(path, items, dry_run)
        verb = "would remove" if dry_run else "removed"
        print(f"  {verb} {total} lines")
        if dry_run:
            print("  (dry run -- stopping before the cascade)")
            return

        subprocess.run(["dune", "build"], check=True)
        print("  build ok")

    raise SystemExit(f"still finding dead lemmas after {max_rounds} rounds")


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--prune", action="store_true", help="delete what is dead, repeat until none is"
    )
    ap.add_argument("-n", "--dry-run", action="store_true", help="change nothing")
    args = ap.parse_args()

    if not os.path.isdir(THEORIES):
        raise SystemExit("run me from the repository root")

    prune(args.dry_run) if args.prune else report()


if __name__ == "__main__":
    main()
