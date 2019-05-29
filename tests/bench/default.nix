{ pkgs ? import ./nixpkgs.nix }:

let
  lean = { stdenv ? pkgs.llvmPackages_7.stdenv }:
    (pkgs.callPackage ../../default.nix { inherit stdenv; }).overrideAttrs (attrs: {
     # pin Lean commit to avoid rebuilds
     # 2019-05-27
     src = builtins.fetchGit { url = ../../.; rev = "0e8abd81bba1b9c06ea7eab23001bbf08ff267dc"; };
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
    unpackCmd = "${pkgs.dpkg}/bin/dpkg -x $src source";
    dontBuild = true;
    installPhase = ''
      mkdir $out
      cp -R . $out
    '';
    preFixup = ''
      wrapProgram $out/usr/bin/mlkit --set PATH ${pkgs.binutils}/bin:${pkgs.pkgsi686Linux.gcc}/bin\
        --set SML_LIB $out/usr/lib/mlkit
    '';
  };
  temci = import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "e397ef9df168d581dcb46de4603088b7a5c6749c"; }) {};
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
  MLKIT = "${mlkit}/usr/bin/mlkit";
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
