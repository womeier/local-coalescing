{
  description = "Verified local-coalescing optimizer for Wasm binaries";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        lib = nixpkgs.lib;
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg: builtins.elem (lib.getName pkg) [ "compcert" ];
        };
        rocqPackages = pkgs.rocqPackages_9_1;
        coqPackages = pkgs.coqPackages_9_1;
        rocq-core = rocqPackages.rocq-core;
        ocaml = rocq-core.ocamlPackages.ocaml;

        mcp = import ./mcp.nix { inherit pkgs lib; };

        wasmcert-master = coqPackages.wasmcert.overrideAttrs (old: {
          version = "master";
          src = pkgs.fetchFromGitHub {
            owner = "wasmcert";
            repo = "wasmcert-coq";
            rev = "5e6df8d60c94aa5dbeff633f5eb48caa6c64c225";
            hash = "sha256-3V7qLB6mXRvqlAxJPV6b8wv0qJBtqrMP0B923wOiMxo=";
          };
        });

        wasm-opt-cert = rocqPackages.mkRocqDerivation {
          pname = "wasm-opt-cert";
          version = "dev";
          src = lib.cleanSource self;
          useDune = true;
          propagatedBuildInputs = [
            wasmcert-master
            coqPackages.ExtLib
            coqPackages.parseque
            coqPackages.mathcomp
            coqPackages.compcert
          ];
          meta = {
            description = "Verified local-coalescing optimizer for Wasm binaries";
            license = lib.licenses.mit;
          };
        };
      in
      {
        packages.default = wasm-opt-cert;
        packages.wasm-opt-cert = wasm-opt-cert;
        packages.rocq-mcp = mcp.rocq-mcp;
        packages.rocq-mcp-wheelhouse = mcp.rocq-mcp-wheelhouse;
        packages.pytanque = mcp.pytanque;
        devShells.default = pkgs.mkShell {
          name = "wasm-opt-cert";
          packages = [
            rocq-core
            # provides the `pet` binary rocq-mcp's interactive tools need.
            rocqPackages.coq-lsp
            wasmcert-master
            pkgs.just
            pkgs.wasm-tools
            # wasm-opt --coalesce-locals, the reference the wat_diff.py
            # report measures our pass against.
            pkgs.binaryen
            pkgs.dune_3
            # `just foo` / `just sha` run the optimized binaries under node,
            # and `just sha_check` drives examples/compare_output.py.
            pkgs.nodejs
            pkgs.python3
            ocaml
            rocq-core.ocamlPackages.findlib
            mcp.rocq-mcp
          ];

          # This Rocq install has no `coqc` symlink — point rocq-mcp at
          # the `rocq` binary directly.
          ROCQ_COQC_BINARY = "${rocq-core}/bin/rocq";
          shellHook = ''
            # ROCQ_WORKSPACE must be the live checkout, not the store copy
            # of ${self} (which omits untracked files).
            export ROCQ_WORKSPACE="$PWD"
            echo "wasm-opt-cert development environment"
            echo "  rocq:     $(rocq --version | head -1)"
            echo "  ocaml:    $(ocaml -version)"
            echo "  dune:     $(dune --version)"
            echo "  rocq-mcp: ${mcp.rocq-mcp.name}"
          '';
        };
      }
    );
}
