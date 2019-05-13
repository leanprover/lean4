{ pkgs ? import ./nixpkgs.nix }:

let
  lean = cmakeFlags: (pkgs.callPackage ../../default.nix { stdenv = pkgs.llvmPackages_7.stdenv; }).overrideAttrs (_: { inherit cmakeFlags; });
  ghc = hsPkgs: (pkgs.haskellPackages.ghcWithPackages hsPkgs).override { ghc = pkgs.haskell.compiler.ghc865; withLLVM = true; };
  ocaml = pkgs.ocaml-ng.ocamlPackages_4_07.ocaml;
  # note that this will need to be compiled from source
  ocamlFlambda = ocaml.override { flambdaSupport = true; };
in {
  buildLean = { name, src, cmakeFlags ? "", leancFlags ? "-O3" }: pkgs.stdenv.mkDerivation {
    inherit name src;
    buildCommand = "${lean cmakeFlags}/bin/lean --cpp=$src.cpp $src && ${lean cmakeFlags}/bin/leanc $src.cpp -o $out";
  };
  buildHs = { name, src, opts, hsPkgs ? (p : []) }: pkgs.stdenv.mkDerivation {
    inherit name src;
    buildCommand = "${ghc hsPkgs}/bin/ghc ${opts} $src -o $out";
  };
  buildOCaml = { name, src, opts }: pkgs.stdenv.mkDerivation {
    inherit name src;
    buildCommand = "${ocaml}/bin/ocamlopt.opt ${opts} $src -o $out";
  };
  buildOCamlFlambda = { name, src, opts }: pkgs.stdenv.mkDerivation {
    inherit name src;
    buildCommand = "${ocamlFlambda}/bin/ocamlopt.opt ${opts} $src -o $out";
  };
}
