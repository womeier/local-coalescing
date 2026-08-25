(lang dune 3.23)
(using rocq 0.13)

; The project/package name must be rocq-wasm-opt: Nix's mkRocqDerivation
; builds with `--only-packages rocq-${pname}`, and dune requires a lone
; package to share the project's name.  (The Rocq theory is still Wasmopt,
; named independently in theories/dune.)
(name rocq-wasm-opt)

(package
 (name rocq-wasm-opt)
 (synopsis "Verified local-coalescing optimization for WebAssembly binaries"))
