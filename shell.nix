let
  flake = (import ./default.nix);
  flakePkgs = flake.packages.${builtins.currentSystem};
in { pkgs ? flakePkgs.nixpkgs, pkgsDist ? pkgs }:
# use `shell` as default
(attribs: attribs.shell // attribs) rec {
  shell = pkgs.mkShell.override {
    stdenv = pkgs.overrideCC pkgs.stdenv flakePkgs.llvmPackages.clang;
  } (rec {
    buildInputs = with pkgs; [
      cmake gmp ccache
      flakePkgs.llvmPackages.llvm  # llvm-symbolizer for asan/lsan
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
  nix = flake.devShell.${builtins.currentSystem};
}
