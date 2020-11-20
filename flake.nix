{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.temci = {
    url = github:parttimenerd/temci;
    flake = false;
  };
  inputs.nix.url = github:NixOS/nix;

  outputs = { self, nixpkgs, flake-utils, temci, nix }: flake-utils.lib.eachDefaultSystem (system:
    with nixpkgs.legacyPackages.${system};
    let
      nix-pinned = writeScriptBin "nix" ''
        #!${bash}/bin/bash
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
    in rec {
      packages = {
        inherit cc lean4-mode buildLeanPackage;
        inherit (lean) stage0 stage1 stage2 stage3;
        inherit (lean.stage1) lean mods test emacs-dev emacs-package;
        temci = (import temci {}).override { doCheck = false; };
        nix = nix-pinned;
        nixpkgs = nixpkgs.legacyPackages.${system};
      };

      defaultPackage = packages.lean;

      checks.lean = packages.test;
    });
}
