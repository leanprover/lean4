{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.temci = {
    url = github:parttimenerd/temci;
    flake = false;
  };
  inputs.nix.url = github:NixOS/nix;
  inputs.mdBook = {
    url = github:leanprover/mdBook;
    flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, temci, nix, mdBook }: flake-utils.lib.eachDefaultSystem (system:
    with nixpkgs.legacyPackages.${system};
    let
      nix-pinned = writeShellScriptBin "nix" ''
        ${nix.defaultPackage.${system}}/bin/nix --experimental-features 'nix-command flakes' --extra-substituters https://lean4.cachix.org/ $@
      '';
      cc = ccacheWrapper.override rec {
        # macOS doesn't like the lld override, but I guess it already uses that anyway
        cc = if system == "x86_64-darwin" then llvmPackages_10.clang else llvmPackages_10.clang.override {
          # linker go brrr
          bintools = llvmPackages_10.lldClang.bintools;
        };
        extraConfig = ''
          export CCACHE_DIR=/nix/var/cache/ccache
          export CCACHE_UMASK=007
          export CCACHE_BASE_DIR=$NIX_BUILD_TOP
          [ -d $CCACHE_DIR ] || exec ${cc}/bin/$(basename "$0") "$@"
        '';
      };
      lean = callPackage (import ./nix/bootstrap.nix) {
        stdenv = overrideCC stdenv cc;
        inherit buildLeanPackage;
      };
      buildLeanPackage = callPackage (import ./nix/buildLeanPackage.nix) {
        inherit (lean) stdenv lean leanc;
        inherit lean-emacs;
        nix = nix-pinned;
      };
      lean4-mode = emacsPackages.melpaBuild {
        pname = "lean4-mode";
        version = "1";
        src = ./lean4-mode;
        packageRequires = with pkgs.emacsPackages.melpaPackages; [ dash dash-functional f flycheck s ];
        recipe = pkgs.writeText "recipe" ''
          (lean4-mode :repo "leanprover/lean4" :fetcher github :files ("*.el"))
        '';
        fileSpecs = [ "*.el" ];
      };
      lean-emacs = emacsWithPackages (epkgs:
        with epkgs; [ dash dash-functional f flycheck s ] ++ [ lean4-mode ]);
      lean-mdbook = mdbook.overrideAttrs (drv: rec {
        name = "lean-${mdbook.name}";
        src = mdBook;
        cargoDeps = drv.cargoDeps.overrideAttrs (_: {
          inherit src;
          outputHash = "sha256-BTm76YxY/tI4Pg53UbR+7KiQydb9L0FGYNZ0UKGyacw=";
        });
        doCheck = false;
      });
      doc = stdenv.mkDerivation {
        name ="lean-doc";
        src = ./doc;
        buildInputs = [ lean-mdbook ];
        buildCommand = ''
          mdbook build -d $out $src
        '';
      };
      # We use a separate derivation instead of `checkPhase` so we can push it but not `doc` to the binary cache
      doc-test = stdenv.mkDerivation {
        name ="lean-doc-test";
        src = ./doc;
        buildInputs = [ lean-mdbook lean.stage1 strace ];
        patchPhase = ''
          patchShebangs test
        '';
        buildPhase = ''
          ./test
          mdbook test
          touch $out
        '';
        dontInstall = true;
      };
    in rec {
      packages = {
        inherit cc lean4-mode buildLeanPackage;
        lean = lean.stage1;
        temci = (import temci {}).override { doCheck = false; };
        nix = nix-pinned;
        nixpkgs = nixpkgs.legacyPackages.${system};
        ciShell = writeShellScriptBin "ciShell" ''
          set -o pipefail
          export PATH=${nix-pinned}/bin:${moreutils}/bin:$PATH
          # prefix lines with cumulative and individual execution time
          "$@" |& ts -i "(%.S)]" | ts -s "[%M:%S"
        '';
        mdbook = lean-mdbook;
        inherit doc doc-test;
      } // lean.stage1 // lean;

      defaultPackage = packages.lean;

      checks.lean = packages.test;
    });
}
