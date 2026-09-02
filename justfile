default: build

build:
    dune build

foo: build
    dune exec ./src/main.exe -- examples/foo.wasm examples/foo_opt.wasm
    (cd examples && node foo.js)

sha: build
    @echo
    @echo "The wasmcert parser is quite slow (sha.wasm ~ 175KB), this may take ~20s..."
    dune exec ./src/main.exe -- examples/sha.wasm examples/sha_opt.wasm
    (cd examples && node sha.js)

sha_check: build
    @echo
    @echo "The wasmcert parser is quite slow (sha.wasm ~ 175KB), this may take ~20s..."
    dune exec ./src/main.exe -- examples/sha.wasm examples/sha_opt.wasm
    (cd examples && python3 compare_output.py sha.js sha_output.txt)

# Same example, but for CI: skips the `build` prerequisite on the
# assumption that `nix build` already produced the extraction at result/.
sha_ci:
    @echo
    @echo "The wasmcert parser is quite slow (sha.wasm ~ 175KB), this may take ~20s..."
    result/bin/wasm-opt-cert examples/sha.wasm examples/sha_opt.wasm
    (cd examples && node sha.js)

# Same, for CI, on the same `nix build` assumption as sha_ci.
sha_wat_diff_ci:
    result/bin/wasm-opt-cert examples/sha.wasm examples/sha_opt.wasm
    python3 examples/wat_diff.py examples/sha.wasm examples/sha_opt.wasm

clean:
    dune clean

opencode:
    nix develop -c opencode

claude:
    nix develop -c claude-sandbox

# Guard regression cases: every optimized output must validate, and the
# behaviour of the two runnable cases must be unchanged.
regress: build
    #!/usr/bin/env bash
    set -euo pipefail
    cd examples/regression
    for f in ssa nonssa loop branch types arms shadow loopdef; do
      dune exec ../../src/main.exe -- $f.wasm $f.opt.wasm > /dev/null
      wasm-tools validate $f.opt.wasm || { echo "  $f: OUTPUT INVALID"; exit 1; }
      echo "  $f: output validates"
    done
    for f in ssa branch arms shadow loopdef; do node equiv.js $f.wasm $f.opt.wasm; done
    echo "regression cases OK"

# What the top-level theorem actually rests on.
#
# Expect WasmCert's own and nothing else -- classical logic and the
# classical reals (via Flocq, for the float operations), functional
# extensionality, and the five SIMD op-string axioms.  Anything named
# Wasmopt.* is a regression.
print_assumptions: build
    #!/usr/bin/env bash
    set -euo pipefail
    printf 'From Wasmopt Require Import toplevel_correct.\nPrint Assumptions coalesce_module_correct.\n' \
      | dune rocq top theories/pipeline.v 2>&1 \
      | grep -vE '^(Fetching opaque|\[Loading ML|Welcome to Rocq|Rocq <|$)'

# Lemmas nothing in the development depends on -- see prune_unused.py, which
# explains what it counts as unused and why the answer comes in two halves.
# Needs the dpdgraph the nix shell provides.
unused: build
    python3 prune_unused.py

# Delete the ones it found nothing referring to, and repeat: deleting cascades,
# since a lemma whose only users were themselves dead becomes visible only once
# they are gone.  Rebuilds between rounds; `git checkout theories/` undoes it.
prune: build
    python3 prune_unused.py --prune
