{
  inputs.lean.url = "git+file:../..";
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.temci.url = github:Kha/temci;
  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.disable-st.url = https://github.com/Kha/lean4/commit/no-st.patch;
  inputs.disable-st.flake = false;

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
    # https://github.com/MLton/mlton/issues/473
    mlton = pkgs.mltonHEAD.override {
      rev = "082087f7f82021a5a84eac0a593b98ba7b16f7fe";
      sha256 = "sha256-AILSBF+Yu+wmeOikwk/binhvjNZD7ZTLnpxnRKijIV0=";
    };
    mlkit = pkgs.mlkit;
    swift = pkgs.swift;
    temci = inputs.temci.packages.${system}.default.override { doCheck = false; };

    default = pkgs.stdenv.mkDerivation rec {
      name = "bench";
      src = ./.;
      LEAN_BIN = "${leanPkgs.lean-all}/bin";
      #LEAN_GCC_BIN = "${lean { stdenv = pkgs.gcc9Stdenv; }}/bin";
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

    lean-variants = pkgs.stdenv.mkDerivation rec {
      name = "lean_bench";
      src = ./.;
      LEAN_BIN = "${leanPkgs.lean-all}/bin";
      LEAN_NO_REUSE_BIN = "${(leanPkgs.override (args: {
        src = pkgs.runCommand "lean-no-reuse-src" {} ''
          cp -r ${args.src} $out
          substituteInPlace $out/src/Lean/Compiler/IR.lean --replace "decls.map Decl.insertResetReuse" "decls"
        '';
      })).stage2.lean-all}/bin";
      LEAN_NO_BORROW_BIN = "${(leanPkgs.override (args: {
        src = pkgs.runCommand "lean-no-borrow-src" {} ''
          cp -r ${args.src} $out
          substituteInPlace $out/src/Lean/Compiler/IR.lean --replace "inferBorrow" "pure"
        '';
      })).stage2.lean-all}/bin";
      LEAN_NO_ST_BIN = "${(leanPkgs.override (args: {
        src = pkgs.runCommand "lean-no-st-src" {} ''
          cp -r ${args.src} $out
          chmod -R u+w $out
          cd $out
          patch -p1 < ${inputs.disable-st}
        '';
      })).lean-all}/bin";
      PARSER_TEST_FILE = ../../src/Init/Prelude.lean;
      buildInputs = with pkgs; [
        ((builtins.elemAt temci.nativeBuildInputs 0).withPackages (ps: [ temci ps.numpy ps.pyyaml ]))
        temci
        pkgs.linuxPackages.perf time unixtools.column
      ];
      patchPhase = ''
        patchShebangs .
      '';
      makeFlags = [ "report_lean.csv" ];
      installPhase = ''
        mkdir $out
        cp -r report *.csv $out
      '';
    };
  };});
}
