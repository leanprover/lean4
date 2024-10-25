{
  description = "Lean development flake. Not intended for end users.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  # old nixpkgs used for portable release with older glibc (2.27)
  inputs.nixpkgs-old.url = "github:NixOS/nixpkgs/nixos-19.03";
  inputs.nixpkgs-old.flake = false;
  # for cadical 1.9.5; sync with CMakeLists.txt
  inputs.nixpkgs-cadical.url = "github:NixOS/nixpkgs/12bf09802d77264e441f48e25459c10c93eada2e";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, nixpkgs-old, flake-utils, ... }@inputs: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old = import nixpkgs-old { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old-aarch = import nixpkgs-old { localSystem.config = "aarch64-unknown-linux-gnu"; };
      pkgsCadical = import inputs.nixpkgs-cadical { inherit system; };
      cadical = if pkgs.stdenv.isLinux then
        # use statically-linked cadical on Linux to avoid glibc versioning troubles
        pkgsCadical.pkgsStatic.cadical.overrideAttrs { doCheck = false; }
      else pkgsCadical.cadical;

      lean-packages = pkgs.callPackage (./nix/packages.nix) { src = ./.; };

      devShellWithDist = pkgsDist: pkgs.mkShell.override {
          stdenv = pkgs.overrideCC pkgs.stdenv lean-packages.llvmPackages.clang;
        } ({
          buildInputs = with pkgs; [
            cmake gmp libuv ccache cadical
            lean-packages.llvmPackages.llvm  # llvm-symbolizer for asan/lsan
            gdb
            tree  # for CI
          ];
          # https://github.com/NixOS/nixpkgs/issues/60919
          hardeningDisable = [ "all" ];
          # more convenient `ctest` output
          CTEST_OUTPUT_ON_FAILURE = 1;
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
          GMP = pkgsDist.gmp.override { withStatic = true; };
          LIBUV = pkgsDist.libuv.overrideAttrs (attrs: {
            configureFlags = ["--enable-static"];
            hardeningDisable = [ "stackprotector" ];
            # Sync version with CMakeLists.txt
            version = "1.48.0";
            src = pkgs.fetchFromGitHub {
              owner = "libuv";
              repo = "libuv";
              rev = "v1.48.0";
              sha256 = "100nj16fg8922qg4m2hdjh62zv4p32wyrllsvqr659hdhjc03bsk";
            };
            doCheck = false;
          });
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
