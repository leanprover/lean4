{ pkgs ? import <nixpkgs> {} }:

let
  lean = pkgs.callPackage ./default.nix {};
  temci = pkgs.callPackage (builtins.fetchGit { url = https://github.com/parttimenerd/temci.git; rev = "1adbe63e3976693eb82ae1bb17b0b17566473853"; }) {};
in pkgs.mkShell rec {
  inputsFrom = [ lean ];
  buildInputs = with pkgs; [ temci clang_7 ccache ninja jemalloc ];
  # TODO: this should not be necessary when leanc starts statically linking binaries
  LD_LIBRARY_PATH = "${pkgs.stdenv.lib.makeLibraryPath buildInputs}:$LD_LIBRARY_PATH";
}
