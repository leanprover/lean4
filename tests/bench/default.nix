{ pkgs ? import ./nixpkgs.nix }:

let
  # pin Lean commit to avoid rebuilds
  # 2019-11-07
  lean = import (builtins.fetchGit { url = ../../.; rev = "3b6755dea1acf0a1a3196131dc3bf9cb7d1ea5c8"; }) {};
  # for binarytrees.hs
  ghcPackages = p: [ p.parallel ];
  ghc = pkgs.haskell.packages.ghc881.ghcWithPackages ghcPackages; #.override { withLLVM = true; };
  ocaml = pkgs.ocaml-ng.ocamlPackages_latest.ocaml;
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
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "ba1505a7c2de471a5821a2643b34de2d1c1af03e"; }) {};
in pkgs.stdenv.mkDerivation rec {
  name = "bench";
  src = pkgs.lib.sourceFilesBySuffices ./. ["Makefile" "leanpkg.path" "temci.yaml" ".py" ".lean" ".hs" ".ml" ".sml"];
  LEAN_BIN = "${lean}/bin";
  #LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
  bootstrapChanges = ''
    make ''${enableParallelBuilding:+-j''${NIX_BUILD_CORES} -l''${NIX_BUILD_CORES}} SHELL=$SHELL update-stage0
    make ''${enableParallelBuilding:+-j''${NIX_BUILD_CORES} -l''${NIX_BUILD_CORES}} SHELL=$SHELL clean-olean
  '';
  LEAN_NO_REUSE_BIN = "${lean.overrideAttrs (attrs: {
    prePatch = ''
      substituteInPlace library/Init/Lean/Compiler/IR/Default.lean --replace "decls.map Decl.insertResetReuse" "decls"
    '';
    preBuild = bootstrapChanges;
  })}/bin";
  LEAN_NO_BORROW_BIN = "${lean.overrideAttrs (attrs: {
    prePatch = ''
      substituteInPlace library/Init/Lean/Compiler/IR/Default.lean --replace "inferBorrow" "pure"
    '';
    preBuild = bootstrapChanges;
  })}/bin";
  LEAN_NO_ST_BIN = "${lean.overrideAttrs (attrs: { prePatch = ''
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
