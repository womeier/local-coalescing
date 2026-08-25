{
  description = "Verified local-coalescing optimizer for Wasm binaries";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        lib = nixpkgs.lib;
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate =
            pkg: builtins.elem (lib.getName pkg) [ "compcert" ];
        };
        rocqPackages = pkgs.rocqPackages_9_1;
        coqPackages = pkgs.coqPackages_9_1;
        rocq-core = rocqPackages.rocq-core;
        ocaml = rocq-core.ocamlPackages.ocaml;
      in
      {
        devShells.default = pkgs.mkShell {
          name = "wasm-opt";
          packages = [
            rocq-core
            coqPackages.wasmcert
            coqPackages.ExtLib
            coqPackages.parseque
            coqPackages.mathcomp
            pkgs.just
            pkgs.wasm-tools
            ocaml
            (rocq-core.ocamlPackages.buildEnv {
              paths = [
                rocq-core.ocamlPackages.dune_3
                rocq-core.ocamlPackages.findlib
              ];
            })
          ];
          shellHook = ''
            echo "wasm-opt development environment"
            echo "  rocq:    $(rocq --version | head -1)"
            echo "  ocaml:   $(ocaml -version)"
            echo "  dune:    $(dune --version)"
          '';
        };
      });
}
