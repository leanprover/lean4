let
  flakePkgs = (import ./default.nix).packages.${builtins.currentSystem};
in { pkgs ? flakePkgs.nixpkgs }:
  # use `shell` as default
  (attribs: attribs.shell // attribs) rec {
  inherit (flakePkgs) temci;
  shell = pkgs.mkShell.override { stdenv = pkgs.overrideCC pkgs.stdenv (flakePkgs.cc.override { extraConfig = ""; }); } rec {
    buildInputs = with pkgs; [ cmake (gmp.override { withStatic = true; }) ccache temci ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];
    # more convenient `ctest` output
    CTEST_OUTPUT_ON_FAILURE = 1;
  };
  nix = pkgs.mkShell {
    buildInputs = [ flakePkgs.nix ];
  };
}
