{ debug ? false, stdenv, lib, cmake, gmp, buildLeanPackage, writeShellScriptBin }:
rec {
  inherit stdenv;
  buildCMake = args: stdenv.mkDerivation ({
    nativeBuildInputs = [ cmake ];
    buildInputs = [ gmp ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];
    cmakeFlags = [ "-DSTAGE=1" "-DPREV_STAGE=./faux-prev-stage" ] ++ lib.optional (args.debug or debug) [ "-DCMAKE_BUILD_TYPE=Debug" ];
    dontStrip = (args.debug or debug);

    postConfigure = ''
      patchShebangs bin
    '';
  } // args // {
    src = args.realSrc or (lib.sourceByRegex args.src [ "[a-z].*" "CMakeLists\.txt" ]);
  });
  leanc = buildCMake {
    name = "leanc";
    src = ../src;
    dontBuild = true;
    installPhase = ''
      mkdir -p $out/bin
      mv include/ $out/
      mv bin/leanc $out/bin/
    '';
  };
  leancpp = buildCMake {
    name = "leancpp";
    src = ../src;
    preConfigure = ''
      echo "target_sources(leancpp PRIVATE shell/lean.cpp)" >> CMakeLists.txt
    '';
    buildFlags = [ "leancpp" ];
    installPhase = ''
      mkdir -p $out
      mv lib/ $out/
    '';
  };
  stage0 = buildCMake {
    name = "lean-stage0";
    src = ../stage0/src;
    debug = false;
    cmakeFlags = [ "-DSTAGE=0" ];
    preConfigure = ''
      ln -s ${../stage0/stdlib} ../stdlib
    '';
    installPhase = ''
      mkdir -p $out/bin
      mv bin/lean $out/bin/
    '';
  };
  stage = { stage, prevStage, self }:
    let
      desc = "stage${toString stage}";
      build = buildLeanPackage.override { lean = prevStage; lean-final = self; };
    in (all: all // all.lean) rec {
      Init = build { name = "Init"; src = ../src; srcDir = "/src"; deps = {}; };
      Std  = build { name = "Std";  src = ../src; srcDir = "/src"; deps = { inherit Init; }; };
      Lean = build { name = "Lean"; src = ../src; srcDir = "/src"; deps = { inherit Init Std; }; };
      inherit (Lean) emacs-dev emacs-package;
      mods = Init.mods // Std.mods // Lean.mods;
      lean = stdenv.mkDerivation {
        # can't use `${desc}` here without breaking `nix run`...
        name = "lean";
        buildCommand = ''
          mkdir -p $out/bin $out/lib/lean
          ln -sf ${leancpp}/lib/lean/* ${Init.staticLib}/* ${Init.modRoot}/* ${Lean.staticLib}/* ${Lean.modRoot}/* ${Std.staticLib}/* ${Std.modRoot}/* $out/lib/lean/
          ${leanc}/bin/leanc -x none -rdynamic -L${gmp}/lib -L$out/lib/lean -L${leancpp}/lib/lean -o $out/bin/lean
          ln -s ${leanc}/bin/leanc $out/bin/
          ln -s ${leanc}/include $out/
        '';
      };
      test = buildCMake {
        name = "lean-test-${desc}";
        realSrc = lib.sourceByRegex ../. [ "src.*" "tests.*" ];
        preConfigure = ''
          cd src
        '';
        postConfigure = ''
          patchShebangs ../../tests
          rm -r bin lib include
          ln -sf ${lean}/* .
        '';
        buildPhase = ''
          ctest --output-on-failure -E 'leancomptest_(doc_example|foreign)' -j$NIX_BUILD_CORES
        '';
        installPhase = ''
          touch $out
        '';
      };
      update-stage0 = writeShellScriptBin "update-stage0" ''
        set -euo pipefail
        rm -r stage0 || true
        mkdir -p stage0/
        cp -r --dereference --no-preserve=all ${Lean.cTree} stage0/stdlib
        # ensure deterministic ordering
        c_files="$(cd ${Lean.cTree}; find . -type l | LC_ALL=C sort | tr '\n' ' ')"
        echo "add_library (stage0 OBJECT $c_files)" > stage0/stdlib/CMakeLists.txt
        # don't copy untracked crap
        git ls-files -z src | xargs -0 -I '{}' bash -c 'mkdir -p `dirname stage0/{}` && cp {} stage0/{}'
        git add stage0
      '';
      update-stage0-commit = writeShellScriptBin "update-stage0-commit" ''
        set -euo pipefail
        ${update-stage0}/bin/update-stage0
        git commit -m "chore: update stage0"
      '';
    };
  stage1 = stage { stage = 1; prevStage = stage0; self = stage1; };
  stage2 = stage { stage = 2; prevStage = stage1; self = stage2; };
  stage3 = stage { stage = 3; prevStage = stage2; self = stage3; };
}
