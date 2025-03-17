{
  description = "Lean development flake. Not intended for end users.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  # old nixpkgs used for portable release with older glibc (2.27)
  inputs.nixpkgs-old.url = "github:NixOS/nixpkgs/nixos-19.03";
  inputs.nixpkgs-old.flake = false;
  # old nixpkgs used for portable release with older glibc (2.26)
  inputs.nixpkgs-older.url = "github:NixOS/nixpkgs/0b307aa73804bbd7a7172899e59ae0b8c347a62d";
  inputs.nixpkgs-older.flake = false;
  # for cadical 2.1.2; sync with CMakeLists.txt by taking commit from https://www.nixhub.io/packages/cadical
  inputs.nixpkgs-cadical.url = "github:NixOS/nixpkgs/199169a2135e6b864a888e89a2ace345703c025d";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old = import inputs.nixpkgs-older { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old-aarch = import inputs.nixpkgs-old { localSystem.config = "aarch64-unknown-linux-gnu"; };
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
            cmake gmp libuv ccache cadical pkg-config
            lean-packages.llvmPackages.llvm  # llvm-symbolizer for asan/lsan
            gdb
            tree  # for CI
          ];
          # https://github.com/NixOS/nixpkgs/issues/60919
          hardeningDisable = [ "all" ];
          # more convenient `ctest` output
          CTEST_OUTPUT_ON_FAILURE = 1;
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
          GMP = (pkgsDist.gmp.override { withStatic = true; }).overrideAttrs (attrs:
            pkgs.lib.optionalAttrs (pkgs.stdenv.system == "aarch64-linux") {
              # would need additional linking setup on Linux aarch64, we don't use it anywhere else either
              hardeningDisable = [ "stackprotector" ];
            });
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
