{ pkgs ? import ./nixpkgs.nix }:

let
  lean = {}:
    (pkgs.callPackage ../../default.nix {}).overrideAttrs (attrs: {
     # pin Lean commit to avoid rebuilds
     # 2019-09-23
     src = builtins.fetchGit { url = ../../.; rev = "345cc22f7935e4b83ed59b1a8fdf98a9241253ae"; };
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
    src = pkgs.fetchzip {
      url = "https://github.com/melsman/mlkit/releases/download/mlkit-4.4.2/mlkit_bin_dist.tgz";
      sha256 = "079299h5m3gkk10qpn2r6va7kjj0sr9z3cs0knjz3qv1cldpzj7x";
    };
    buildInputs = [ pkgs.makeWrapper ];
    dontBuild = true;
    installPhase = ''
      mkdir $out
      cp -R . $out
    '';
    preFixup = ''
      wrapProgram $out/bin/mlkit --set PATH ${pkgs.binutils}/bin:${pkgs.gcc}/bin\
        --set SML_LIB $out/lib/mlkit
    '';
  };
  swift = pkgs.swift;
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "74086d20659731a16d0c04e9022c20fc63958322"; }) {};
in pkgs.stdenv.mkDerivation rec {
  name = "bench";
  src = pkgs.lib.sourceFilesBySuffices ./. ["Makefile" "leanpkg.path" "temci.yaml" ".py" ".lean" ".hs" ".ml" ".sml"];
  LEAN_BIN = "${lean {}}/bin";
  #LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
  LEAN_NO_REUSE_BIN = "${(lean {}).overrideAttrs (attrs: {
    prePatch = ''
      substituteInPlace library/init/lean/compiler/ir/default.lean --replace "decls.map Decl.insertResetReuse" "decls"
    '';
    preBuild = ''
      # bootstrap changes
      make update-stage0
      make clean-olean
    '';
  })}/bin";
  LEAN_NO_BORROW_BIN = "${(lean {}).overrideAttrs (attrs: {
    prePatch = ''
      substituteInPlace library/init/lean/compiler/ir/default.lean --replace "inferBorrow" "pure"
    '';
    preBuild = ''
      # bootstrap changes
      make update-stage0
      make clean-olean
    '';
  })}/bin";
  LEAN_NO_ST_BIN = "${(lean {}).overrideAttrs (attrs: { prePatch = ''
    substituteInPlace src/runtime/object.h --replace "c_init_mem_kind = object_memory_kind::STHeap" "c_init_mem_kind = object_memory_kind::MTHeap"
  ''; })}/bin";
  GHC = "${ghc}/bin/ghc";
  OCAML = "${ocaml}/bin/ocamlopt.opt";
  #OCAML_FLAMBDA = "${ocamlFlambda}/bin/ocamlopt.opt";
  MLTON_BIN = "${mlton}/bin";
  MLKIT = "${mlkit}/bin/mlkit";
  SWIFTC = "${swift}/bin/swiftc";
  TEMCI = "${temci}/bin/temci";
  buildInputs = with pkgs; [
    gmp # needed by leanc
    (python3.withPackages (ps: [ temci ]))
    temci
    pkgs.linuxPackages.perf time unixtools.column
  ];
  patchPhase = ''
    patchShebangs .
  '';
  installPhase = ''
    mkdir $out
    cp -r report *.csv $out
  '';
}
