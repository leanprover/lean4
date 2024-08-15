{
  description = "Lean development flake. Not intended for end users.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  # old nixpkgs used for portable release with older glibc (2.27)
  inputs.nixpkgs-old.url = "github:NixOS/nixpkgs/nixos-19.03";
  inputs.nixpkgs-old.flake = false;
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, nixpkgs-old, flake-utils, ... }@inputs: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old = import nixpkgs-old { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old-aarch = import nixpkgs-old { localSystem.config = "aarch64-unknown-linux-gnu"; };

      lean-packages = pkgs.callPackage (./nix/packages.nix) { src = ./.; };

      devShellWithDist = pkgsDist: pkgs.mkShell.override {
          stdenv = pkgs.overrideCC pkgs.stdenv lean-packages.llvmPackages.clang;
        } ({
          buildInputs = with pkgs; [
            cmake gmp libuv ccache
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
          LIBUV = pkgsDist.libuv.overrideAttrs (attrs: { configureFlags = ["--enable-static"]; });
          GLIBC = pkgsDist.glibc;
          GLIBC_DEV = pkgsDist.glibc.dev;
          GCC_LIB = pkgsDist.gcc.cc.lib;
          ZLIB = pkgsDist.zlib;
          GDB = pkgsDist.gdb;
        });
    in {
      packages = {
        # to be removed when Nix CI is not needed anymore
        inherit (lean-packages) cacheRoots test update-stage0-commit ciShell;
        deprecated = lean-packages;
      };

      # The default development shell for working on lean itself
      devShells.default = devShellWithDist pkgs;
      devShells.oldGlibc = devShellWithDist pkgsDist-old;
      devShells.oldGlibcAArch = devShellWithDist pkgsDist-old-aarch;
    });
}
