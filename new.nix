{ debug ? false, stdenv, stdenvNoCC, lib, runCommand, runCommandLocal, cmake, coreutils, binutils, gmp, bash, gnused, symlinkJoin }:
with builtins; rec {
  # "Init.Core" ~> "Init/Core.lean"
  modToLean = mod: replaceStrings ["."] ["/"] mod + ".lean";
  depRoot = name: deps: symlinkJoin { inherit name; paths = lib.attrValues deps; };
  buildLeanPackage = { name, src, lean, deps }:
    let
    fakeDepRoot = mod: runCommandLocal "${name}-dep-root" {} ''
      mkdir $out
      cd $out
      mkdir ${lib.concatStringsSep " " ([name] ++ attrNames deps)}
    '';
    # build a file containing the module names of all immediate dependencies of `mod`
    leanDeps = mod: derivation {
      inherit (stdenv) system;
      name ="${mod}-deps";
      src = src + ("/" + modToLean mod);
      builder = stdenv.shell;
      args = [ "-c" ''
export LEAN_PATH=${fakeDepRoot mod};
${lean}/bin/lean --deps $src | ${gnused}/bin/sed "s!$LEAN_PATH/!!;s!/!.!g;s!.olean!!" > $out
      '' ];
      preferLocalBuild = true;
      allowSubstitutes = false;
    };
    #${lean}/bin/lean --deps ${src}/${modToLean mod} | sed -n "s!$LEAN_PATH/!!;\!^${name}/!{s!/!.!g;s!.olean!!;p}" > $out
    # build module (.olean and .c) given derivations of all (transitive) dependencies
    buildMod = mod: deps:
      let relpath = modToLean mod; in
      stdenvNoCC.mkDerivation {
      name = "${mod}";
      LEAN_PATH = depRoot mod deps;
      relpath = relpath;
      outputs = [ "out" "c" ];
      buildInputs = [ lean ];
      src = src + ("/" + relpath);
      buildCommand = ''
        mkdir -p $(dirname $relpath) $out/$(dirname $relpath) $c
        cp $src $relpath
        lean -o $out/''${relpath%.lean}.olean -c $c/out.c $relpath
      '';
    };
    compileMod = mod: drv: runCommand "${mod}-cc" {
      hardeningDisable = [ "all" ];
      buildInputs = [ lean ];
    } ''
      mkdir -p $out
      ln -s ${drv.c}/out.c .
      leanc -c -o $out/out.o out.c ${if debug then "-g" else "-O3 -DNDEBUG"}
    '';
    singleton = name: value: listToAttrs [ { inherit name value; } ];
    # Recursively build `mod` and its dependencies. `modMap` maps module names to
    # `{ deps, drv }` pairs of a derivation and its transitive dependencies (as a nested
    # mapping from module names to derivations). It is passed linearly through the
    # recursion to memoize common dependencies.
    buildModAndDeps = mod: modMap: if modMap ? ${mod} then modMap else
      let
        immDeps = filter (p: p != "") (lib.splitString "\n" (readFile (leanDeps mod)));
        modMap' = lib.foldr buildModAndDeps modMap immDeps;
        deps = lib.foldr (dep: depMap: depMap // modMap'.${dep}.deps // { ${dep} = modMap'.${dep}; }) {} immDeps;
      in modMap' // { ${mod} = buildMod mod deps // { inherit deps; }; };
    in rec {
      mods      = buildModAndDeps name (lib.foldr (dep: depMap: depMap // dep.mods) {} (attrValues deps));
      modRoot   = depRoot name mods;
      objects   = mapAttrs compileMod mods;
      staticLib = runCommand "${name}-lib" { buildInputs = [ binutils ]; } ''
mkdir $out
ar rcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/out.o") (attrValues objects))}
      '';
    };
  stage = { stage, src ? ./src, prevStage ? null }:
    let
      desc = "stage${toString stage}";
      Init = buildLeanPackage { name = "Init"; src = src; lean = prevStage; deps = {}; };
      Std  = buildLeanPackage { name = "Std";  src = src; lean = prevStage; deps = { inherit Init; }; };
      Lean = buildLeanPackage { name = "Lean"; src = src; lean = prevStage; deps = { inherit Init Std; }; };
      leanBin = stdenv.mkDerivation {
        name = "lean-bin-${desc}";

        src = lib.sourceByRegex src [ "[a-z].*" "CMakeLists\.txt" "CTestCustom\.cmake\.in" ];

        nativeBuildInputs = [ cmake ];
        buildInputs = [ gmp ];
        dontStrip = debug;
        # https://github.com/NixOS/nixpkgs/issues/60919
        hardeningDisable = [ "all" ];

        cmakeFlags = [ (if prevStage != null then "-DSTAGE=1" else "-DSTAGE=0") ] ++
                     lib.optional (prevStage != null) [ "-DPREV_STAGE=${prevStage}" ] ++
                     lib.optional debug [ "-DCMAKE_BUILD_TYPE=Debug" ];
        preConfigure =
          if prevStage != null then ''
            substituteInPlace CMakeLists.txt --replace '$(MAKE) -f ''${CMAKE_BINARY_DIR}/stdlib.make' 'ln -s ${Init.staticLib}/* ${Std.staticLib}/* ${Lean.staticLib}/* ''${CMAKE_BINARY_DIR}/lib/lean'
          '' else ''
            ln -s ${./stage0/stdlib} ../stdlib
          '';
        postConfigure = ''
          patchShebangs bin
        '';
        buildFlags = [ "lean" ];
        installPhase = ''
          mkdir $out
          mv bin include $out/
          mv lib/lean $out/lib/
        '';
      };
      bundle = runCommand "lean-${desc}" {} ''
        mkdir -p $out/lib/lean
        ln -s ${Init.staticLib}/* ${Std.staticLib}/* ${Lean.staticLib}/* ${Lean.modRoot}/* $out/lib/lean
        cp -r ${leanBin}/bin $out/bin
        ln -s ${leanBin}/include $out/include
      '';
      test = stdenv.mkDerivation {
        name = "lean-test-${desc}";

        inherit src;
        nativeBuildInputs = leanBin.nativeBuildInputs ++ leanBin.buildInputs ++ [ bash ];

        postConfigure = ''
          patchShebangs tests
          #ln -s ${install}/bin ../../bin
          #ln -s ${install}/bin/lean shell/lean
          #rm -r ../../library
          #ln -s ${install}/lib/lean/library ../../library
        '';
        buildPhase = ''
          ctest --output-on-failure -E style_check -j$NIX_BUILD_CORES
        '';
      };
    in { inherit leanBin Init Std Lean; } // bundle;
  stage0 = (stage { stage = 0; src = ./stage0/src; }).leanBin;
  stage1 = stage { stage = 1; prevStage = stage0; };
  stage2 = stage { stage = 2; prevStage = stage1; };
  stage3 = stage { stage = 3; prevStage = stage2; };
}
