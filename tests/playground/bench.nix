{ pkgs ? import ./nixpkgs.nix }:

let
  lean = { cmakeFlags ? "", stdenv ? pkgs.llvmPackages_7.stdenv }:
    (pkgs.callPackage ../../default.nix { inherit stdenv; }).overrideAttrs (attrs: {
      inherit cmakeFlags;
     # pin Lean commit to avoid rebuilds
     # 2019-05-24
     src = builtins.fetchGit { url = ../../.; rev = "074002eb847b6f4fbaf2484c928c86baadf66a42"; };
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
  mlton = pkgs.mlton;
  mlkit = pkgs.stdenv.mkDerivation {
    name = "mlkit";
    src = builtins.fetchurl {
      name = "mlkit-deb";
      url = "https://launchpad.net/~pmunksgaard/+archive/ubuntu/mlkit/+files/mlkit_4.3.18-0~12~ubuntu18.10.1_amd64.deb";
      sha256 = "0wbz4l1i8z8kv3qkd1hc06lpqbfq1kndr8n68339mlpgzriz01vy";
    };
    buildInputs = [ pkgs.makeWrapper ];
    buildCommand = ''
      mkdir $out
      ${pkgs.dpkg}/bin/dpkg -x $src $out/
      wrapProgram $out/usr/bin/mlkit --set PATH ${pkgs.binutils}/bin:${pkgs.pkgsi686Linux.gcc}/bin\
        --set SML_LIB $out/usr/lib/mlkit
    '';
  };
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "90534eb5846dae0e9a540234d6a3b1017e928603"; }) {};
in pkgs.stdenv.mkDerivation rec {
  name = "bench";
  src = pkgs.lib.sourceFilesBySuffices ./. ["Makefile" "leanpkg.path" "temci.yaml" ".py" ".lean" ".hs" ".ml"];
  LEAN_BIN = "${lean {}}/bin";
  LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
  GHC = "${ghc}/bin/ghc";
  OCAML = "${ocaml}/bin/ocamlopt.opt";
  OCAML_FLAMBDA = "${ocamlFlambda}/bin/ocamlopt.opt";
  MLTON = "${mlton}/bin/mlton";
  MLKIT = "${mlkit}/usr/bin/mlkit";
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
