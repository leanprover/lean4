{ pkgs ? import ./nixpkgs.nix }:

let
  lean = { cmakeFlags ? "", stdenv ? pkgs.llvmPackages_7.stdenv }:
    (pkgs.callPackage ../../default.nix { inherit stdenv; }).overrideAttrs (attrs: {
      inherit cmakeFlags;
     # pin Lean commit to avoid rebuilds
     # 2019-05-17
     src = builtins.fetchGit { url = ../../.; rev = "48ed3c5307c7504826c343c3d5d62f5381789b78"; };
    });
  # for binarytrees.hs
  ghcPackages = p: [ p.parallel ];
  ghc = (pkgs.haskellPackages.ghcWithPackages ghcPackages).override {
    ghc = pkgs.haskell.compiler.ghc865;
    withLLVM = true;
  };
  ocaml = pkgs.ocaml-ng.ocamlPackages_4_07.ocaml;
  # note that this will need to be compiled from source
  ocamlFlambda = ocaml.override { flambdaSupport = true; };
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "e7b5edb1229c63b52cca25ddefee884a84a9e5c6"; }) {};
in pkgs.stdenv.mkDerivation rec {
  name = "bench";
  src = pkgs.lib.sourceFilesBySuffices ./. ["Makefile" "leanpkg.path" "temci.yaml" ".py" ".lean" ".hs" ".ml"];
  LEAN_BIN = "${lean {}}/bin";
  LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
  GHC = "${ghc}/bin/ghc";
  OCAML = "${ocaml}/bin/ocamlopt.opt";
  OCAML_FLAMBDA = "${ocamlFlambda}/bin/ocamlopt.opt";
  TEMCI = "${temci}/bin/temci";
  buildInputs = with pkgs; [
    gmp # needed by leanc
    (python3.withPackages (ps: [ temci ]))
    temci
    pkgs.linuxPackages.perf time
  ];
  patchPhase = ''
    patchShebangs .
  '';
  installPhase = ''
    mkdir $out
    cp -r report *.csv $out
  '';
}
