let
  flakePkgs = (import ./default.nix).packages.${builtins.currentSystem};
in { pkgs ? flakePkgs.nixpkgs, llvmPackages ? null, static ? false }:
# use `shell` as default
(attribs: attribs.shell // attribs) rec {
  inherit (flakePkgs) temci;
  shell = pkgs.mkShell.override {
    stdenv = pkgs.overrideCC pkgs.stdenv (if llvmPackages == null
                                          then flakePkgs.llvmPackages
                                          else pkgs.${"llvmPackages_${llvmPackages}"}).clang;
  } rec {
    buildInputs = with pkgs; [
      cmake
      (gmp.override { withStatic = static; })
      llvm
      ccache
      temci
      # LLVM dependencies
      (if static then zlib.static else zlib)
      (ncurses.override { enableStatic = static; })
    ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];
    # more convenient `ctest` output
    CTEST_OUTPUT_ON_FAILURE = 1;
    shellHook = ''
      export LEAN_SRC_PATH="$PWD/src"
    '';
  };
  nix = pkgs.mkShell {
    buildInputs = [ flakePkgs.nix ];
    shellHook = ''
      export LEAN_SRC_PATH="$PWD/src"
    '';
  };
}
