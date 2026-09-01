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
    dune exec ./src/main.exe -- examples/sha.wasm examples/sha_opt.wasm
    (cd examples && python3 compare_output.py sha.js sha_output.txt)

# Same example, but for CI: skips the `build` prerequisite on the
# assumption that `nix build` already produced the extraction at result/.
sha_ci:
    @echo
    @echo "The wasmcert parser is quite slow (sha.wasm ~ 175KB), this may take ~20s..."
    result/bin/wasm-opt-cert examples/sha.wasm examples/sha_opt.wasm
    (cd examples && node sha.js)

# sha.wasm printed as .wat before and after the pass, plus a per-function
# count of the locals each side declares, next to what
# `wasm-opt --coalesce-locals` gets on the same input.
sha_wat_diff: build
    dune exec ./src/main.exe -- examples/sha.wasm examples/sha_opt.wasm
    python3 examples/wat_diff.py examples/sha.wasm examples/sha_opt.wasm

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
    for f in ssa nonssa loop branch types arms shadow; do
      dune exec ../../src/main.exe -- $f.wasm $f.opt.wasm > /dev/null
      wasm-tools validate $f.opt.wasm || { echo "  $f: OUTPUT INVALID"; exit 1; }
      echo "  $f: output validates"
    done
    for f in ssa branch arms shadow; do node equiv.js $f.wasm $f.opt.wasm; done
    echo "regression cases OK"

# What the top-level theorem actually rests on.  This, not grepping for
# Admitted, is what decides whether the development is complete: an admit
# can hide behind a definition, or an assumption be introduced anywhere
# below.
#
# Expect WasmCert's own and nothing else -- classical logic and the
# classical reals (via Flocq, for the float operations), functional
# extensionality, and the five SIMD op-string axioms.  Anything named
# Wasmopt.* is a regression.
#
# Note it is `dune rocq top`, not `dune coq top`: the latter does not
# recognise the rocq.theory stanza.  It is pointed at pipeline.v because it
# refuses to Require a library with the same name as the file it was given,
# so any module of the theory other than toplevel_correct will do.
print_assumptions: build
    #!/usr/bin/env bash
    set -euo pipefail
    printf 'From Wasmopt Require Import toplevel_correct.\nPrint Assumptions coalesce_module_correct.\n' \
      | dune rocq top theories/pipeline.v 2>&1 \
      | grep -vE '^(Fetching opaque|\[Loading ML|Welcome to Rocq|Rocq <|$)'
