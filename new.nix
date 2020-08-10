{ debug ? false, stdenv, stdenvNoCC, lib, runCommand, runCommandLocal, cmake, coreutils, binutils, gmp, bash, symlinkJoin }:
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
    leanDeps = mod: runCommandLocal "${mod}-deps" {} ''
export LEAN_PATH=${fakeDepRoot mod};
${lean}/bin/lean --deps ${src}/${modToLean mod} | sed "s!$LEAN_PATH/!!;s!/!.!g;s!.olean!!" > $out
    '';
    #${lean}/bin/lean --deps ${src}/${modToLean mod} | sed -n "s!$LEAN_PATH/!!;\!^${name}/!{s!/!.!g;s!.olean!!;p}" > $out
    # build module (.olean and .c) given derivations of all (transitive) dependencies
    buildMod = mod: deps: stdenvNoCC.mkDerivation rec {
      name = "${mod}";
      relpath = modToLean mod;
      LEAN_PATH = depRoot mod deps;
      outputs = [ "out" "c" ];
      buildInputs = [ lean ];
      buildCommand = ''
        mkdir -p $out/$(dirname $relpath) $c
        lean --root=${src} -o $out/''${relpath%.lean}.olean -c $c/out.c ${src}/$relpath
      '';
    };
    compileMod = mod: drv: runCommand "${mod}-cc" {
      buildInputs = [ lean ];
    } ''
      mkdir -p $out
      leanc -c -o $out/out.o ${drv.c}/out.c ${if debug then "-g" else "-O3 -DNDEBUG"}
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
      objects   = mapAttrs compileMod mods;
      staticLib = runCommand "${name}-lib" { buildInputs = [ binutils ]; } ''
mkdir $out
ar rcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/out.o") (attrValues objects))}
      '';
    };
  stage = { stage, src ? ./src, prevStage ? null }:
    let build = rec {
      desc = "stage${toString stage}";
      leanBin = stdenv.mkDerivation rec {
        name = "lean-${desc}";

        inherit src;

        nativeBuildInputs = [ cmake ];
        buildInputs = [ gmp ];
        dontStrip = debug;
        # https://github.com/NixOS/nixpkgs/issues/60919
        hardeningDisable = [ "all" ];

        cmakeFlags = [ "-DSTAGE=${toString stage}" "-DLIB_SOURCE_DIR=${src}" ] ++
                     lib.optional (prevStage != null) "-DPREV_STAGE=${prevStage}" ++
                     lib.optional debug [ "-DCMAKE_BUILD_TYPE=Debug" ];
        preConfigure = if stage == 0 then "ln -s ${./stage0/stdlib} ../stdlib" else "";
        postConfigure = ''
          patchShebangs bin
        '';
        buildFlags = [ "lean" "VERBOSE=1" ];
        installPhase = ''
          mkdir $out
          cp -r bin include $out/
          cp -r lib/lean $out/lib/
        '';
      };
      Init = buildLeanPackage { name = "Init"; src = ./src; lean = leanBin; deps = {}; };
      Std  = buildLeanPackage { name = "Std";  src = ./src; lean = leanBin; deps = { inherit Init; }; };
      Lean = buildLeanPackage { name = "Lean"; src = ./src; lean = leanBin; deps = { inherit Init Std; }; };
      stdlib = { inherit Init Std Lean; };
      #stdlib = runCommand "lean-stdlib-${desc}" {} ''
#mkdir -p $out/lib/lean
#ln -s ${Init.staticLib}/* ${Std.staticLib}/* ${Lean.staticLib}/* $out/lib/lean
      #'';
      postBuild = lib.makeOverridable ({ stdlib }:
        let postBuild = {
        #ln -s ${stdlib} $out/lib/lean/library
              install = runCommand "lean-install-${desc}" {} ''
        mkdir -p $out/lib/lean
        ln -s ${stdlib.Init.staticLib}/* ${stdlib.Std.staticLib}/* ${stdlib.Lean.staticLib}/* $out/lib/lean
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
            }; in postBuild // postBuild.install) { inherit stdlib; };
    }; in build // build.postBuild;
  stage0 = stage { stage = 0; src = ./stage0/src; };
  stage1 = stage { stage = 1; prevStage = stage0; };
  stage0p5 = stage1 // stage1.postBuild.override { inherit (stage0) stdlib; };
  stage2 = stage { stage = 2; prevStage = stage1; };
}
