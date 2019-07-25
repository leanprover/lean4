{ pkgs ? import <nixpkgs> {} }:

let
  lean = pkgs.callPackage ./default.nix {};
  temci = pkgs.callPackage (builtins.fetchGit { url = https://github.com/parttimenerd/temci.git; rev = "2facd7c78ab35722f34db1d42883ec02f8a0de23"; }) {};
in pkgs.mkShell rec {
  inputsFrom = [ lean ];
  buildInputs = with pkgs; [ temci clang_7 ccache ninja ];
  # https://github.com/NixOS/nixpkgs/issues/60919
  hardeningDisable = [ "all" ];
  # TODO: this should not be necessary when leanc starts statically linking binaries
  LD_LIBRARY_PATH = "${pkgs.stdenv.lib.makeLibraryPath buildInputs}:$LD_LIBRARY_PATH";
}
