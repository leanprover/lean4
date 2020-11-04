{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;

  outputs = { self, nixpkgs }:
    with import nixpkgs { system = "x86_64-linux"; };
    let
      cc = ccacheWrapper.override rec {
        cc = llvmPackages_10.clang.override {
          # linker go brrr
          bintools = llvmPackages_10.lldClang.bintools;
        };
        extraConfig = ''
          export CCACHE_DIR=/var/cache/ccache
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
        # can't use `epkgs`???
        with emacsPackages.melpaPackages; [ dash dash-functional f flycheck s ] ++ [ lean4-mode ]);
  in {
    packages.x86_64-linux = {
      inherit (lean.stage1.Lean) mods leanInteractive emacs;
      lean = lean.stage1 // lean // { inherit buildLeanPackage; };
    };

    defaultPackage.x86_64-linux = self.packages.x86_64-linux.lean;

    checks.x86_64-linux.lean = self.packages.x86_64-linux.lean.test;
  };
}
