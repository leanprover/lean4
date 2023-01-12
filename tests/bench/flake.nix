{
  inputs.lean.url = "../..";
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.temci.url = github:Kha/temci;
  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.mltonNixpkgs.url = github:NixOS/nixpkgs/nixos-21.11;

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system: { packages = rec {
    leanPkgs = inputs.lean.packages.${system};
    pkgs = inputs.nixpkgs.legacyPackages.${system};
    ocamlPkgs = pkgs.ocaml-ng.ocamlPackages_latest;
    # https://github.com/ocaml/opam-repository/pull/22688
    lockfree = ocamlPkgs.lockfree.overrideAttrs (_: rec {
      version = "0.2.0";
      src = pkgs.fetchurl {
        url = "https://github.com/ocaml-multicore/lockfree/releases/download/v${version}/lockfree-${version}.tbz";
        hash = "sha256-cEwgaTRiSNOJkTQIw2SDTBvEbepdQRwL7dg2hosh4yE=";
      };
    });
    domainslib = ocamlPkgs.domainslib.overrideAttrs (_: {
      propagatedBuildInputs = [ lockfree ];
    });
    # for binarytrees.hs
    ghcPackages = p: [ p.parallel ];
    ghc = pkgs.haskell.packages.ghc944.ghcWithPackages ghcPackages; #.override { withLLVM = true; };
    ocaml = ocamlPkgs.ocaml;
    # note that this will need to be compiled from source
    ocamlFlambda = ocaml.override { flambdaSupport = true; };
    mlton = inputs.mltonNixpkgs.legacyPackages.${system}.mlton;
    mlkit = pkgs.mlkit;
    swift = pkgs.swift;
    temci = inputs.temci.packages.${system}.default.override { doCheck = false; };

    default = pkgs.stdenv.mkDerivation rec {
      name = "bench";
      src = ./.;
      LEAN_BIN = "${leanPkgs.lean-all}/bin";
      #LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
      #LEAN_NO_REUSE_BIN = "${lean.overrideAttrs (attrs: {
      #  prePatch = ''
      #substituteInPlace src/Lean/Compiler/IR.lean --replace "decls.map Decl.insertResetReuse" "decls"
      #  '';
      #  buildFlags = [ "stage1.5" ];
      #  installFlags = [ "-C stage1.5" ];
      #})}/bin";
      #LEAN_NO_BORROW_BIN = "${lean.overrideAttrs (attrs: {
      #  prePatch = ''
      #substituteInPlace src/Lean/Compiler/IR.lean --replace "inferBorrow" "pure"
      #  '';
      #  buildFlags = [ "stage1.5" ];
      #  installFlags = [ "-C stage1.5" ];
      #})}/bin";
      #LEAN_NO_ST_BIN = "${lean.overrideAttrs (attrs: { patches = [ ./disable-st.patch ]; })}/bin";
      PARSER_TEST_FILE = ../../src/Init/Core.lean;
      GHC = "${ghc}/bin/ghc";
      OCAML = "${ocaml}/bin/ocamlopt.opt";
      #OCAML_FLAMBDA = "${ocamlFlambda}/bin/ocamlopt.opt";
      MLTON_BIN = "${mlton}/bin";
      MLKIT = "${mlkit}/bin/mlkit";
      SWIFTC = "${swift}/bin/swiftc";
      TEMCI = "${temci}/bin/temci";
      buildInputs = with pkgs; [
        ((builtins.elemAt temci.nativeBuildInputs 0).withPackages (ps: [ temci ps.numpy ps.pyyaml ]))
        ocaml
        ocamlPkgs.findlib
        domainslib
        temci
        pkgs.linuxPackages.perf time unixtools.column
      ];
      patchPhase = ''
        patchShebangs .
      '';
      makeFlags = [ "report_cross.csv" ];
      installPhase = ''
        mkdir $out
        cp -r report *.csv $out
      '';
    };
  };});
}
