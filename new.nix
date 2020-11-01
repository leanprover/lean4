{ debug ? false, stdenv, stdenvNoCC, lib, runCommand, runCommandLocal, cmake, coreutils, binutils, gmp, bash, gnused, symlinkJoin, writeScript, lndir }:
with builtins; rec {
  # "Init.Core" ~> "Init/Core.lean"
  modToLean = mod: replaceStrings ["."] ["/"] mod + ".lean";
  mkDerivation = args@{ buildCommand, ... }: derivation (args // {
    inherit stdenv;
    inherit (stdenv) system;
    builder = stdenv.shell;
    args = [ "-c" ''
export PATH=${coreutils}/bin
set -euo pipefail
${buildCommand}
    '' ];
  });
  depRoot = name: deps: mkDerivation {
    name = "${name}-deps";
    inherit deps;
    depRoots = map (drv: drv.LEAN_PATH) deps;
    buildCommand = ''
      mkdir -p $out
      for i in $depRoots; do
        cp -dru --no-preserve=mode $i/. $out
      done
      for i in $deps; do
        cp -drsu --no-preserve=mode $i/. $out
      done
    '';
  };
  buildLeanPackage = { name, src, lean, leanc ? lean, deps }:
    let
    fakeDepRoot = runCommandLocal "${name}-dep-root" {} ''
      mkdir $out
      cd $out
      mkdir ${lib.concatStringsSep " " ([name] ++ attrNames deps)}
    '';
    # build a file containing the module names of all immediate dependencies of `mod`
    leanDeps = mod: mkDerivation {
      name ="${mod}-deps";
      src = src + ("/" + modToLean mod);
      buildCommand = ''
export LEAN_PATH=${fakeDepRoot};
${lean}/bin/lean --deps $src | ${gnused}/bin/sed "s!$LEAN_PATH/!!;s!/!.!g;s!.olean!!" > $out
      '';
      preferLocalBuild = true;
      allowSubstitutes = false;
    };
    #${lean}/bin/lean --deps ${src}/${modToLean mod} | sed -n "s!$LEAN_PATH/!!;\!^${name}/!{s!/!.!g;s!.olean!!;p}" > $out
    # build module (.olean and .c) given derivations of all (transitive) dependencies
    buildMod = mod: deps: let relpath = modToLean mod; in mkDerivation {
      name = "${mod}";
      LEAN_PATH = depRoot mod deps;
      inherit lean relpath;
      outputs = [ "out" "c" ];
      src = src + ("/" + relpath);
      buildCommand = ''
        export PATH=${coreutils}/bin
        mkdir -p $(dirname $relpath) $out/$(dirname $relpath) $c
        cp $src $relpath
        $lean/bin/lean -o $out/''${relpath%.lean}.olean -c $c/out.c $relpath
      '';
    } // {
      inherit deps;
    };
    compileMod = mod: drv: mkDerivation {
      name = "${mod}-cc";
      src = "${drv.c}/out.c";
      hardeningDisable = [ "all" ];
      buildCommand = ''
        export PATH=${coreutils}/bin
        mkdir -p $out
        ln -s $src out.c
        ${leanc}/bin/leanc -c -o $out/out.o out.c ${if debug then "-g" else "-O3 -DNDEBUG"}
      '';
    };
    singleton = name: value: listToAttrs [ { inherit name value; } ];
    # Recursively build `mod` and its dependencies. `modMap` maps module names to
    # `{ deps, drv }` pairs of a derivation and its transitive dependencies (as a nested
    # mapping from module names to derivations). It is passed linearly through the
    # recursion to memoize common dependencies.
    buildModAndDeps = mod: modMap: if modMap ? ${mod} then modMap else
      let
        deps = filter (p: p != "") (lib.splitString "\n" (readFile (leanDeps mod)));
        modMap' = lib.foldr buildModAndDeps modMap deps;
      in modMap' // { ${mod} = buildMod mod (map (dep: modMap'.${dep}) deps); };
    in rec {
      mods      = buildModAndDeps name (lib.foldr (dep: depMap: depMap // dep.mods) {} (attrValues deps));
      modRoot   = depRoot name [ mods.${name} ];
      objects   = mapAttrs compileMod mods;
      staticLib = runCommand "${name}-lib" { buildInputs = [ binutils ]; } ''
mkdir $out
ar rcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/out.o") (attrValues objects))}
      '';
    };
  buildCMake = args: stdenv.mkDerivation ({
    cmakeFlags = [ "-DSTAGE=1" "-DPREV_STAGE=./faux-prev-stage" ] ++ lib.optional (args.debug or debug) [ "-DCMAKE_BUILD_TYPE=Debug" ];
    dontStrip = (args.debug or debug);
    postConfigure = ''
      patchShebangs bin
    '';
  } // args // {
    src = args.realSrc or (lib.sourceByRegex args.src [ "[a-z].*" "CMakeLists\.txt" ]);

    nativeBuildInputs = [ cmake ];
    buildInputs = [ gmp ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];

    installPhase = ''
      mkdir $out
      mv bin/ lib/ include/ $out/
    '';
  });
  leanc = buildCMake {
    name = "leanc";
    src = ./src;
    dontBuild = true;
  };
  leancpp = buildCMake {
    name = "leancpp";
    src = ./src;
    preConfigure = ''
      echo "target_sources(leancpp PRIVATE shell/lean.cpp)" >> CMakeLists.txt
    '';
    buildFlags = [ "leancpp" ];
  };
  stage0 = buildCMake {
    name = "lean-stage0";
    src = ./stage0/src;
    debug = false;
    cmakeFlags = [ "-DSTAGE=0" ];
    preConfigure = ''
      ln -s ${./stage0/stdlib} ../stdlib
    '';
  };
  stage = { stage, prevStage }:
    let desc = "stage${toString stage}";
    in (all: all // all.lean) rec {
      Init = buildLeanPackage { name = "Init"; src = ./src; lean = prevStage; inherit leanc; deps = {}; };
      Std  = buildLeanPackage { name = "Std";  src = ./src; lean = prevStage; inherit leanc; deps = { inherit Init; }; };
      Lean = buildLeanPackage { name = "Lean"; src = ./src; lean = prevStage; inherit leanc; deps = { inherit Init Std; }; };
      lean = mkDerivation {
        name = "lean-${desc}";
        buildCommand = ''
          mkdir -p $out/bin $out/lib/lean
          ln -sf ${leancpp}/lib/lean/* ${Init.staticLib}/* ${Init.modRoot}/* ${Lean.staticLib}/* ${Lean.modRoot}/* ${Std.staticLib}/* ${Std.modRoot}/* $out/lib/lean
          ${leancpp}/bin/leanc -x none -rdynamic -L${gmp}/lib -L$out/lib/lean ${leancpp}/lib/lean/* -o $out/bin/lean
          ln -s ${leancpp}/bin/{leanc,lean-gdb.py} $out/bin/
          ln -s ${leancpp}/include $out/include
        '';
      };
      test = buildCMake {
        name = "lean-test-${desc}";
        realSrc = lib.sourceByRegex ./. [ "src.*" "tests.*" ];
        preConfigure = ''
          cd src
        '';
        postConfigure = ''
          patchShebangs ../../tests
          rm -r bin lib include
          ln -sf ${lean}/* .
        '';
        buildPhase = ''
          ctest --output-on-failure -E leancomptest_foreign -j$NIX_BUILD_CORES
        '';
      };
    };
  stage1 = stage { stage = 1; prevStage = stage0; };
  stage2 = stage { stage = 2; prevStage = stage1; };
  stage3 = stage { stage = 3; prevStage = stage2; };
}
