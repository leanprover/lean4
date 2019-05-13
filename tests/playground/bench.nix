{ pkgs ? import ./nixpkgs.nix }:

let
  lean = { cmakeFlags ? "", stdenv ? pkgs.llvmPackages_7.stdenv }:
    (pkgs.callPackage ../../default.nix { inherit stdenv; }).overrideAttrs (attrs: {
      inherit cmakeFlags;
      # pin Lean commit to avoid rebuilds
      # 2019-05-12
      src = builtins.fetchGit { url = ../../.; rev = "de5b68f1262214eecf3d59d7540ed0e9447edf7b"; };
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
in pkgs.stdenv.mkDerivation rec {
  name = "bench";
  LEAN_BIN = "${lean {}}/bin";
  LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
  GHC = "${ghc}/bin/ghc";
  OCAML = "${ocaml}/bin/ocamlopt.opt";
  OCAML_FLAMBDA = "${ocamlFlambda}/bin/ocamlopt.opt";
  buildInputs = with pkgs; [ bench gmp python3 ];
  buildCommand = ''
    make
    mkdir $out
    cp *.csv $out
  '';
#in {
#  buildLean = { name, src, cmakeFlags ? "", leancFlags ? "-O3" }: pkgs.stdenv.mkDerivation {
#    inherit name src;
#    buildCommand = "${lean cmakeFlags}/bin/lean --cpp=$src.cpp $src && ${lean cmakeFlags}/bin/leanc $src.cpp -o $out";
#  };
#  buildHs = { name, src, opts, hsPkgs ? (p : []) }: pkgs.stdenv.mkDerivation {
#    inherit name src;
#    buildCommand = "${ghc hsPkgs}/bin/ghc ${opts} $src -o $out";
#  };
#  buildOCaml = { name, src, opts }: pkgs.stdenv.mkDerivation {
#    inherit name src;
#    buildCommand = "${ocaml}/bin/ocamlopt.opt ${opts} $src -o $out";
#  };
#  buildOCamlFlambda = { name, src, opts }: pkgs.stdenv.mkDerivation {
#    inherit name src;
#    buildCommand = "${ocamlFlambda}/bin/ocamlopt.opt ${opts} $src -o $out";
#  };
}
