{
  inputs.lean.url = "../..";
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.temci.url = github:Kha/temci;
  inputs.swiftPkgs.url = github:NixOS/nixpkgs/007ccf2f4f1da567903ae392cbf19966eb30cf20;

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system: { packages = rec {
    leanPkgs = inputs.lean.packages.${system};
    pkgs = leanPkgs.nixpkgs;
    # for binarytrees.hs
    ghcPackages = p: [ p.parallel ];
    ghc = pkgs.haskell.packages.ghc921.ghcWithPackages ghcPackages; #.override { withLLVM = true; };
    ocaml = pkgs.ocaml; # pkgs.ocaml-ng.ocamlPackages_latest.ocaml;
    # note that this will need to be compiled from source
    ocamlFlambda = ocaml.override { flambdaSupport = true; };
    mlton = pkgs.mlton;
    mlkit = pkgs.mlkit;
    swift = inputs.swiftPkgs.legacyPackages.${system}.swift; # pkgs.swift;
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
        (python3.withPackages (ps: [ temci ps.numpy ps.pyyaml ]))
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
