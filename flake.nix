{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  # old nixpkgs used for portable release with older glibc (2.27)
  inputs.nixpkgs-old.url = "github:NixOS/nixpkgs/nixos-19.03";
  inputs.nixpkgs-old.flake = false;
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nix.url = "github:NixOS/nix";
  inputs.lean4-mode = {
    url = "github:leanprover/lean4-mode";
    flake = false;
  };
  # used *only* by `stage0-from-input` below
  #inputs.lean-stage0 = {
  #  url = github:leanprover/lean4;
  #  inputs.nixpkgs.follows = "nixpkgs";
  #  inputs.flake-utils.follows = "flake-utils";
  #  inputs.nix.follows = "nix";
  #  inputs.lean4-mode.follows = "lean4-mode";
  #};

  outputs = { self, nixpkgs, nixpkgs-old, flake-utils, nix, lean4-mode, ... }@inputs: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        inherit system;
        # for `vscode-with-extensions`
        config.allowUnfree = true;
      };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old = import nixpkgs-old { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old-aarch = import nixpkgs-old { localSystem.config = "aarch64-unknown-linux-gnu"; };

      lean-packages = pkgs.callPackage (./nix/packages.nix) { src = ./.; inherit nix lean4-mode; };

      devShellWithDist = pkgsDist: pkgs.mkShell.override {
          stdenv = pkgs.overrideCC pkgs.stdenv lean-packages.llvmPackages.clang;
        } ({
          buildInputs = with pkgs; [
            cmake gmp ccache
            lean-packages.llvmPackages.llvm  # llvm-symbolizer for asan/lsan
            gdb
            # TODO: only add when proven to not affect the flakification
            #pkgs.python3
            tree  # for CI
          ];
          # https://github.com/NixOS/nixpkgs/issues/60919
          hardeningDisable = [ "all" ];
          # more convenient `ctest` output
          CTEST_OUTPUT_ON_FAILURE = 1;
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
          GMP = pkgsDist.gmp.override { withStatic = true; };
          GLIBC = pkgsDist.glibc;
          GLIBC_DEV = pkgsDist.glibc.dev;
          GCC_LIB = pkgsDist.gcc.cc.lib;
          ZLIB = pkgsDist.zlib;
          GDB = pkgsDist.gdb;
        });
    in {
      packages = lean-packages // rec {
        debug = lean-packages.override { debug = true; };
        stage0debug = lean-packages.override { stage0debug = true; };
        asan = lean-packages.override { extraCMakeFlags = [ "-DLEAN_EXTRA_CXX_FLAGS=-fsanitize=address" "-DLEANC_EXTRA_FLAGS=-fsanitize=address" "-DSMALL_ALLOCATOR=OFF" "-DSYMBOLIC=OFF" ]; };
        asandebug = asan.override { debug = true; };
        tsan = lean-packages.override {
          extraCMakeFlags = [ "-DLEAN_EXTRA_CXX_FLAGS=-fsanitize=thread" "-DLEANC_EXTRA_FLAGS=-fsanitize=thread" "-DCOMPRESSED_OBJECT_HEADER=OFF" ];
          stage0 = (lean-packages.override {
            # Compressed headers currently trigger data race reports in tsan.
            # Turn them off for stage 0 as well so stage 1 can read its own stdlib.
            extraCMakeFlags = [ "-DCOMPRESSED_OBJECT_HEADER=OFF" ];
          }).stage1;
        };
        tsandebug = tsan.override { debug = true; };
        stage0-from-input = lean-packages.override {
          stage0 = pkgs.writeShellScriptBin "lean" ''
            exec ${inputs.lean-stage0.packages.${system}.lean}/bin/lean -Dinterpreter.prefer_native=false "$@"
          '';
        };
        inherit self;
      };
      defaultPackage = lean-packages.lean-all;

      # The default development shell for working on lean itself
      devShells.default = devShellWithDist pkgs;
      devShells.oldGlibc = devShellWithDist pkgsDist-old;
      devShells.oldGlibcAArch = devShellWithDist pkgsDist-old-aarch;

      checks.lean = lean-packages.test;
    }) // rec {
      templates.pkg = {
        path = ./nix/templates/pkg;
        description = "A custom Lean package";
      };

      defaultTemplate = templates.pkg;
    };
}
