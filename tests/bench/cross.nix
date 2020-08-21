{ pkgs ? import ./nixpkgs.nix }:

let
  # pin Lean commit to avoid rebuilds
  # 2020-08-18
  lean = import (builtins.fetchGit { url = ../../.; rev = "d059d28c220247d51310c4ea437807c3446d36d7"; }) {};
  # for binarytrees.hs
  ghcPackages = p: [ p.parallel ];
  ghc = pkgs.haskell.packages.ghc884.ghcWithPackages ghcPackages; #.override { withLLVM = true; };
  ocaml = pkgs.ocaml-ng.ocamlPackages_4_11.ocaml;
  # note that this will need to be compiled from source
  ocamlFlambda = ocaml.override { flambdaSupport = true; };
  mlton = pkgs.mlton;
  mlkit = pkgs.stdenv.mkDerivation {
    name = "mlkit";
    src = builtins.fetchTarball {
      url = "https://github.com/melsman/mlkit/releases/download/v4.5.0/mlkit_bin_dist.tgz";
      sha256 = "1nrk2klhrr2xcm83y601w6dffl756qfk4kgvn3rkjlp7b2i8r8mr";
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
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "64eca12970e8096aa20557c35fd089dd6c668e1b"; }) { inherit pkgs; };
in pkgs.stdenv.mkDerivation rec {
  name = "bench";
  src = pkgs.lib.sourceFilesBySuffices ./. ["Makefile" "leanpkg.path" "temci.yaml" ".py" ".lean" ".hs" ".ml" ".sml"];
  LEAN_BIN = "${lean}/bin";
  #LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
  LEAN_NO_REUSE_BIN = "${lean.overrideAttrs (attrs: {
    prePatch = ''
substituteInPlace src/Lean/Compiler/IR.lean --replace "decls.map Decl.insertResetReuse" "decls"
    '';
    buildFlags = [ "stage1.5" ];
    installFlags = [ "-C stage1.5" ];
  })}/bin";
  LEAN_NO_BORROW_BIN = "${lean.overrideAttrs (attrs: {
    prePatch = ''
substituteInPlace src/Lean/Compiler/IR.lean --replace "inferBorrow" "pure"
    '';
    buildFlags = [ "stage1.5" ];
    installFlags = [ "-C stage1.5" ];
  })}/bin";
  LEAN_NO_ST_BIN = "${lean.overrideAttrs (attrs: { patches = [ ./disable-st.patch ]; })}/bin";
  PARSER_TEST_FILE = lean.src + "/src/Init/Core.lean";
  GHC = "${ghc}/bin/ghc";
  OCAML = "${ocaml}/bin/ocamlopt.opt";
  #OCAML_FLAMBDA = "${ocamlFlambda}/bin/ocamlopt.opt";
  MLTON_BIN = "${mlton}/bin";
  MLKIT = "${mlkit}/bin/mlkit";
  SWIFTC = "${swift}/bin/swiftc";
  TEMCI = "${temci}/bin/temci";
  buildInputs = with pkgs; [
    gmp # needed by leanc
    (python37.withPackages (ps: [ temci ps.numpy ps.pyyaml ]))
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
