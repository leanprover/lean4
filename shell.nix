{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ? pkgs.llvmPackages_8 } @ args:

let
  lean = import ./default.nix args;
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "ba1505a7c2de471a5821a2643b34de2d1c1af03e"; }) { inherit pkgs; };
in pkgs.mkShell.override { stdenv = lean.stdenv; } rec {
  inputsFrom = [ lean ];
  buildInputs = with pkgs; [ temci ccache ninja ];
  # https://github.com/NixOS/nixpkgs/issues/60919
  hardeningDisable = [ "all" ];
  # TODO: this should not be necessary when leanc starts statically linking binaries
  LD_LIBRARY_PATH = "${pkgs.stdenv.lib.makeLibraryPath buildInputs}:$LD_LIBRARY_PATH";
}
