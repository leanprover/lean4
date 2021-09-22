{ debug ? false, stage0debug ? false, extraCMakeFlags ? [],
  stdenv, lib, cmake, gmp, gnumake, bash, buildLeanPackage, writeShellScriptBin, runCommand, symlinkJoin, lndir, perl,
  ... } @ args:
with builtins;
rec {
  inherit stdenv;
  buildCMake = args: stdenv.mkDerivation ({
    nativeBuildInputs = [ cmake ];
    buildInputs = [ gmp ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];
    dontStrip = (args.debug or debug);

    postConfigure = ''
      patchShebangs bin
    '';
  } // args // {
    src = args.realSrc or (lib.sourceByRegex args.src [ "[a-z].*" "CMakeLists\.txt" ]);
    cmakeFlags = (args.cmakeFlags or [ "-DSTAGE=1" "-DPREV_STAGE=./faux-prev-stage" "-DUSE_GITHASH=OFF" ]) ++ (args.extraCMakeFlags or extraCMakeFlags) ++ lib.optional (args.debug or debug) [ "-DCMAKE_BUILD_TYPE=Debug" ];
  });
  lean-bin-tools-unwrapped = buildCMake {
    name = "lean-bin-tools";
    realSrc = lib.sourceByRegex ../src [ "CMakeLists\.txt" "bin.*" "include.*" ".*\.in" ];
    preConfigure = ''
      touch empty.cpp
      sed -i 's/find_package.*//;s/add_subdirectory.*//;s/set(LEAN_OBJS.*/set(LEAN_OBJS empty.cpp)/' CMakeLists.txt
    '';
    dontBuild = true;
    installPhase = ''
      mkdir $out
      mv bin/ include/ share/ $out/
      substituteInPlace $out/bin/leanmake --replace "make" "${gnumake}/bin/make"
      substituteInPlace $out/share/lean/lean.mk --replace "/usr/bin/env bash" "${bash}/bin/bash"
    '';
  };
  leancpp = buildCMake {
    name = "leancpp";
    src = ../src;
    buildFlags = [ "leancpp" "leanrt" "leanrt_initial-exec" "shell" ];
    installPhase = ''
      mkdir -p $out
      mv lib/ $out/
      mv shell/CMakeFiles/shell.dir/lean.cpp.o $out/lib
      mv runtime/libleanrt_initial-exec.a $out/lib
    '';
  };
  # rename derivation so `nix run` uses the right executable name but we still see the stage in the build log
  wrapStage = stage: runCommand "lean" {} ''
    ln -s ${stage} $out
  '';
  stage0 = wrapStage (args.stage0 or (buildCMake {
    name = "lean-stage0";
    realSrc = ../stage0/src;
    debug = stage0debug;
    cmakeFlags = [ "-DSTAGE=0" ];
    extraCMakeFlags = [];
    preConfigure = ''
      ln -s ${../stage0/stdlib} ../stdlib
    '';
    installPhase = ''
      mkdir -p $out/bin $out/lib/lean
      mv bin/lean $out/bin/
      mv lib/lean/libleanshared.* $out/lib/lean
   '' + lib.optionalString stdenv.isDarwin ''
      for lib in $(otool -L $out/bin/lean | tail -n +2 | cut -d' ' -f1); do
        if [[ "$lib" == *lean* ]]; then install_name_tool -change "$lib" "$out/lib/lean/$(basename $lib)" $out/bin/lean; fi
      done
      otool -L $out/bin/lean
    '';
  }));
  stage = { stage, prevStage, self }:
    let
      desc = "stage${toString stage}";
      build = args: buildLeanPackage.override {
        lean = prevStage;
        leanc = lean-bin-tools-unwrapped;
        # use same stage for retrieving dependencies
        lean-leanDeps = stage0;
        lean-final = self;
      } ({
        src = ../src;
        fullSrc = ../.;
        inherit debug;
      } // args);
    in (all: all // all.lean) rec {
      inherit (Lean) emacs-dev emacs-package vscode-dev vscode-package;
      Init = build { name = "Init"; deps = []; };
      Std  = build { name = "Std";  deps = [ Init ]; };
      Lean = build { name = "Lean"; deps = [ Init Std ]; };
      stdlib = [ Init Std Lean ];
      Leanpkg = build { name = "Leanpkg"; deps = stdlib; linkFlags = ["-L${gmp}/lib -L${leanshared}"]; };
      extlib = stdlib ++ [ Leanpkg ];
      stdlibLinkFlags = "-L${gmp}/lib -L${Init.staticLib} -L${Std.staticLib} -L${Lean.staticLib} -L${leancpp}/lib/lean";
      leanshared = runCommand "leanshared" { buildInputs = [ stdenv.cc ]; } ''
        mkdir $out
        LEAN_CC=${stdenv.cc}/bin/cc ${lean-bin-tools-unwrapped}/bin/leanc -shared ${lib.optionalString stdenv.isLinux "-Bsymbolic"} \
          ${if stdenv.isDarwin then "-Wl,-force_load,${Init.staticLib}/libInit.a -Wl,-force_load,${Std.staticLib}/libStd.a -Wl,-force_load,${Lean.staticLib}/libLean.a -Wl,-force_load,${leancpp}/lib/lean/libleancpp.a ${leancpp}/lib/libleanrt_initial-exec.a -lc++"
            else "-Wl,--whole-archive -lInit -lStd -lLean -lleancpp ${leancpp}/lib/libleanrt_initial-exec.a -Wl,--no-whole-archive -lstdc++"} -lm ${stdlibLinkFlags} \
          -o $out/libleanshared${stdenv.hostPlatform.extensions.sharedLibrary}
      '';
      mods = Init.mods // Std.mods // Lean.mods;
      leanc = writeShellScriptBin "leanc" ''
        LEAN_CC=${stdenv.cc}/bin/cc ${lean-bin-tools-unwrapped}/bin/leanc ${stdlibLinkFlags} -L${leanshared} "$@"
      '';
      lean = runCommand "lean" {} ''
        mkdir -p $out/bin
        ${leanc}/bin/leanc ${leancpp}/lib/lean.cpp.o ${leanshared}/* -o $out/bin/lean
      '';
      leanpkg = Leanpkg.executable.withSharedStdlib;
      # derivation following the directory layout of the "basic" setup, mostly useful for running tests
      lean-all = wrapStage(stdenv.mkDerivation {
        name = "lean-${desc}";
        buildCommand = ''
          mkdir -p $out/bin $out/lib/lean
          ln -sf ${leancpp}/lib/lean/* ${lib.concatMapStringsSep " " (l: "${l.modRoot}/* ${l.staticLib}/*") (lib.reverseList extlib)} $out/lib/lean/
          # put everything in a single final derivation so `IO.appDir` references work
          cp ${lean}/bin/lean ${leanpkg}/bin/leanpkg $out/bin
          # NOTE: first `bin/leanc` wins in case of `lndir`
          for i in ${leanc} ${lean-bin-tools-unwrapped}; do
            ${lndir}/bin/lndir -silent $i $out
          done
        '';
      });
      test = buildCMake {
        name = "lean-test-${desc}";
        realSrc = lib.sourceByRegex ../. [ "src.*" "tests.*" ];
        buildInputs = [ gmp perl ];
        preConfigure = ''
          cd src
        '';
        postConfigure = ''
          patchShebangs ../../tests
          rm -r bin lib include share
          ln -sf ${lean-all}/* .
        '';
        buildPhase = ''
          ctest --output-on-failure -E 'leancomptest_(doc_example|foreign)' -j$NIX_BUILD_CORES
        '';
        installPhase = ''
          touch $out
        '';
      };
      update-stage0 =
        let cTree = symlinkJoin { name = "cs"; paths = map (l: l.cTree) stdlib; }; in
        writeShellScriptBin "update-stage0" ''
          CSRCS=${cTree} CP_PARAMS="--dereference --no-preserve=all" ${../script/update-stage0}
        '';
      update-stage0-commit = writeShellScriptBin "update-stage0-commit" ''
        set -euo pipefail
        ${update-stage0}/bin/update-stage0
        git commit -m "chore: update stage0"
      '';
      benchmarks =
        let
          entries = attrNames (readDir ../tests/bench);
          leanFiles = map (n: elemAt n 0) (filter (n: n != null) (map (match "(.*)\.lean") entries));
        in lib.genAttrs leanFiles (n: (buildLeanPackage {
          name = n;
          src = filterSource (e: _: baseNameOf e == "${n}.lean") ../tests/bench;
        }).executable);
    };
  stage1 = stage { stage = 1; prevStage = stage0; self = stage1; };
  stage2 = stage { stage = 2; prevStage = stage1; self = stage2; };
  stage3 = stage { stage = 3; prevStage = stage2; self = stage3; };
}
