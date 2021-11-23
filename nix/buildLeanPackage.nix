{ lean, lean-leanDeps ? lean, lean-final ? lean, leanc,
  stdenv, lib, coreutils, gnused, writeShellScriptBin, bash, lean-emacs, lean-vscode, nix, substituteAll, symlinkJoin, linkFarmFromDrvs,
  runCommand, gmp, ... }:
let lean-final' = lean-final; in
lib.makeOverridable (
{ name, src,  fullSrc ? src, 
  # Lean dependencies. Each entry should be an output of buildLeanPackage.
  deps ? [ lean.Lean lean.Leanpkg ],
  # Static library dependencies. Each derivation `static` should contain a static library in the directory `${static}`.
  staticLibDeps ? [],
  # Shared library dependencies included at interpretation with --load-dynlib and linked to. Each derivation `shared` should contain a 
  # shared library at the path `${shared}/${shared.libName or shared.name}` and a name to link to like `-l${shared.linkName or shared.name}`.
  # These libs are also linked to in packages that depend on this one.
  nativeSharedLibs ? [],
  # Lean plugin dependencies. Each derivation `plugin` should contain a plugin library at path `${plugin}/${plugin.name}`.
  pluginDeps ? [],
  debug ? false, leanFlags ? [], leancFlags ? [], linkFlags ? [], executableName ? lib.toLower name,
  srcTarget ? "..#stage0", srcArgs ? "(\${args[*]})", lean-final ? lean-final' }:
with builtins; let
  # "Init.Core" ~> "Init/Core"
  modToPath = mod: replaceStrings ["."] ["/"] mod;
  modToLean = mod: modToPath mod + ".lean";
  mkBareDerivation = args@{ buildCommand, ... }: derivation (args // {
    inherit stdenv;
    inherit (stdenv) system;
    buildInputs = (args.buildInputs or []) ++ [ coreutils ];
    builder = stdenv.shell;
    args = [ "-c" ''
      for pkg in $buildInputs; do
        export PATH=$PATH:$pkg/bin
      done
      set -euo pipefail
      ${buildCommand}
    '' ];
  });
  runBareCommand = name: args: buildCommand: mkBareDerivation (args // { inherit name buildCommand; });
  runBareCommandLocal = name: args: buildCommand: runBareCommand name (args // {
    preferLocalBuild = true;
    allowSubstitutes = false;
  }) buildCommand;
  depRoot = name: deps: mkBareDerivation {
    name = "${name}-depRoot";
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
    preferLocalBuild = true;
    allowSubstitutes = false;
  };
  srcRoot = src;

  # A flattened list of Lean-module dependencies (`deps`)
  allExternalDeps = lib.foldr (dep: allExternalDeps: allExternalDeps // { ${dep.name} = dep; } // dep.allExternalDeps) {} deps;
  allNativeSharedLibs =
    lib.unique (lib.flatten (nativeSharedLibs ++ (map (dep: dep.allNativeSharedLibs or []) (attrValues allExternalDeps))));
  # A flattened list of all static library dependencies: this and every dep module's explicitly provided `staticLibDeps`, 
  # plus every dep module itself: `dep.staticLib`
  allStaticLibDeps = 
    lib.unique (lib.flatten (staticLibDeps ++ (map (dep: [dep.staticLib] ++ dep.staticLibDeps or []) (attrValues allExternalDeps))));

  pathOfSharedLib = dep: dep.libPath or "${dep}/${dep.libName or dep.name}";

  leanPluginFlags = lib.concatStringsSep " " (map (dep: "--plugin=${pathOfSharedLib dep}") pluginDeps);
  leanLoadDynlibFlags = lib.concatStringsSep " " (map (dep: "--load-dynlib=${pathOfSharedLib dep}") allNativeSharedLibs);

  fakeDepRoot = runBareCommandLocal "${name}-dep-root" {} ''
    mkdir $out
    cd $out
    mkdir ${lib.concatStringsSep " " ([name] ++ attrNames allExternalDeps)}
  '';
  print-lean-deps = writeShellScriptBin "print-lean-deps" ''
    export LEAN_PATH=${fakeDepRoot}
    ${lean-leanDeps}/bin/lean --deps --stdin | ${gnused}/bin/sed "s!$LEAN_PATH/!!;s!/!.!g;s!.olean!!"
  '';
  # build a file containing the module names of all immediate dependencies of `mod`
  leanDeps = mod: mkBareDerivation {
    name ="${mod}-deps";
    src = src + ("/" + modToLean mod);
    buildInputs = [ print-lean-deps ];
    buildCommand = ''
      print-lean-deps < $src > $out
    '';
    preferLocalBuild = true;
    allowSubstitutes = false;
  };
  # build module (.olean and .c) given derivations of all (transitive) dependencies
  buildMod = mod: deps: mkBareDerivation rec {
    name = "${mod}";
    LEAN_PATH = depRoot mod deps;
    relpath = modToPath mod;
    buildInputs = [ lean ];
    leanPath = relpath + ".lean";
    src = srcRoot + ("/" + leanPath);
    outputs = [ "out" "c" ];
    oleanPath = relpath + ".olean";
    cPath = relpath + ".c";
    inherit leanFlags leanPluginFlags leanLoadDynlibFlags;
    buildCommand = ''
      mkdir -p $(dirname $relpath) $out/$(dirname $relpath) $c/$(dirname $relpath)
      cp $src $leanPath
      lean -o $out/$oleanPath -c $c/$cPath $leanPath $leanFlags $leanPluginFlags $leanLoadDynlibFlags
    '';
  } // {
    inherit deps;
  };
  compileMod = mod: drv: mkBareDerivation {
    name = "${mod}-cc";
    buildInputs = [ leanc stdenv.cc ];
    hardeningDisable = [ "all" ];
    oPath = drv.relpath + ".o";
    inherit leancFlags;
    buildCommand = ''
      mkdir -p $out/$(dirname ${drv.relpath})
      # make local "copy" so `drv`'s Nix store path doesn't end up in ccache's hash
      ln -s ${drv.c}/${drv.cPath} src.c
      # on the other hand, a debug build is pretty fast anyway, so preserve the path for gdb
      leanc -c -o $out/$oPath $leancFlags -fPIC ${if debug then "${drv.c}/${drv.cPath} -g -v" else "src.c -O3 -DNDEBUG"}
    '';
  };
  singleton = name: value: listToAttrs [ { inherit name value; } ];
  externalModMap = lib.foldr (dep: depMap: depMap // dep.mods) {} (attrValues allExternalDeps);
  # Recursively build `mod` and its dependencies. `modMap` maps module names to
  # `{ deps, drv }` pairs of a derivation and its transitive dependencies (as a nested
  # mapping from module names to derivations). It is passed linearly through the
  # recursion to memoize common dependencies.
  buildModAndDeps = mod: modMap: if modMap ? ${mod} || externalModMap ? ${mod} then modMap else
    let
      deps = filter (p: p != "") (lib.splitString "\n" (readFile (leanDeps mod)));
      modMap' = lib.foldr buildModAndDeps modMap deps;
    in modMap' // { ${mod} = buildMod mod (map (dep: if modMap' ? ${dep} then modMap'.${dep} else externalModMap.${dep}) deps); };
  makeEmacsWrapper = name: lean: writeShellScriptBin name ''
    ${lean-emacs}/bin/emacs --eval "(progn (setq lean4-rootdir \"${lean}\"))" "$@"
  '';
  makeVSCodeWrapper = name: lean: writeShellScriptBin name ''
    PATH=${lean}/bin:$PATH ${lean-vscode}/bin/code "$@"
  '';
  printPaths = deps: writeShellScriptBin "print-paths" ''
    echo '${toJSON { oleanPath = [(depRoot "print-paths" deps)]; srcPath = ["."] ++ map (dep: dep.src) (attrValues allExternalDeps); }}'
  '';
  makePrintPathsFor = deps: mods: printPaths deps // mapAttrs (_: mod: makePrintPathsFor (deps ++ [mod]) mods) mods;
  mods      = buildModAndDeps name {};
  allLinkFlags = lib.foldr (shared: acc: acc ++ [ "-L${shared}" "-l${shared.linkName or shared.name}" ]) linkFlags allNativeSharedLibs;
in rec {
  inherit name lean deps staticLibDeps allNativeSharedLibs allLinkFlags allExternalDeps print-lean-deps src mods;
  modRoot   = depRoot name [ mods.${name} ];
  cTree     = symlinkJoin { name = "${name}-cTree"; paths = map (mod: mod.c) (attrValues mods); };
  objects   = mapAttrs compileMod mods;
  oTree     = symlinkJoin { name = "${name}-oTree"; paths = (attrValues objects); };
  staticLib = runCommand "${name}-lib" { buildInputs = [ stdenv.cc.bintools.bintools ]; } ''
    mkdir -p $out
    ar Trcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/${drv.oPath}") (attrValues objects))};
  '';
  sharedLib = runCommand "${name}.so" { buildInputs = [ stdenv.cc gmp ]; } ''
    mkdir -p $out/lib
    ${leanc}/bin/leanc -fPIC -shared \
      -Wl,--whole-archive ${staticLib}/* -Wl,--no-whole-archive\
      ${lib.concatStringsSep " " (map (d: "${d}/*.a") allStaticLibDeps)} \
      -o $out/${name}.so
  '';
  executable = runCommand executableName { buildInputs = [ stdenv.cc leanc ]; } ''
    mkdir -p $out/bin
    leanc -Wl,--start-group ${staticLib}/* ${lib.concatStringsSep " " (map (d: "${d}/*.a") allStaticLibDeps)} -Wl,--end-group \
      -o $out/bin/${executableName} \
      ${lib.concatStringsSep " " allLinkFlags}
  '' // {
    withSharedStdlib = runCommand executableName { buildInputs = [ stdenv.cc leanc ]; } ''
      mkdir -p $out/bin
      leanc ${staticLib}/* -lleanshared \
        -o $out/bin/${executableName} \
        ${lib.concatStringsSep " " allLinkFlags}
    '';
  };

  lean-package = writeShellScriptBin "lean" ''
    LEAN_PATH=${modRoot}:$LEAN_PATH LEAN_SRC_PATH=${src}:$LEAN_SRC_PATH ${lean-final}/bin/lean "$@"
  '';
  emacs-package = makeEmacsWrapper "emacs-package" lean-package;
  vscode-package = makeVSCodeWrapper "vscode-package" lean-package;

  print-paths = makePrintPathsFor [] (mods // externalModMap);
  # `lean` wrapper that dynamically runs Nix for the actual `lean` executable so the same editor can be
  # used for multiple projects/after upgrading the `lean` input/for editing both stage 1 and the tests
  lean-bin-dev = substituteAll {
    name = "lean";
    dir = "bin";
    src = ./lean-dev.in;
    isExecutable = true;
    srcRoot = fullSrc;  # use root flake.nix in case of Lean repo
    inherit bash nix srcTarget srcArgs;
  };
  lake-dev = substituteAll {
    name = "lake";
    dir = "bin";
    src = ./lake-dev.in;
    isExecutable = true;
    srcRoot = fullSrc;  # use root flake.nix in case of Lean repo
    inherit bash nix srcTarget srcArgs;
  };
  lean-dev = symlinkJoin { name = "lean-dev"; paths = [ lean-bin-dev lake-dev ]; };
  emacs-dev = makeEmacsWrapper "emacs-dev" lean-dev;
  vscode-dev = makeVSCodeWrapper "vscode-dev" lean-dev;
})
