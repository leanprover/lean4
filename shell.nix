{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ?pkgs.llvmPackages_9 } @ args:

let
  lean = import ./default.nix args;
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "4cae802606b871021394e250a280a2154b92f44b"; }) { inherit pkgs; };
in pkgs.mkShell.override { stdenv = lean.stdenv; } rec {
  inputsFrom = [ lean ];
  buildInputs = with pkgs; [ temci ];
  # https://github.com/NixOS/nixpkgs/issues/60919
  hardeningDisable = [ "all" ];
  # more convenient `ctest` output
  CTEST_OUTPUT_ON_FAILURE = 1;
}
