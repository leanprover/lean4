{ lean, lean-leanDeps ? lean, lean-final ? lean, leanc,
  stdenv, lib, coreutils, gnused, writeShellScriptBin, bash, lean-emacs, lean-vscode, nix, substituteAll, symlinkJoin, linkFarmFromDrvs,
  runCommand, gmp, darwin, ... }:
let lean-final' = lean-final; in
lib.makeOverridable (
{ name, src,  fullSrc ? src, 
  # Lean dependencies. Each entry should be an output of buildLeanPackage.
  deps ? [ lean.Lean ],
  # Static library dependencies. Each derivation `static` should contain a static library in the directory `${static}`.
  staticLibDeps ? [],
  # Whether to wrap static library inputs in a -Wl,--start-group [...] -Wl,--end-group to ensure dependencies are resolved.
  groupStaticLibs ? false,
  # Shared library dependencies included at interpretation with --load-dynlib and linked to. Each derivation `shared` should contain a 
  # shared library at the path `${shared}/${shared.libName or shared.name}` and a name to link to like `-l${shared.linkName or shared.name}`.
  # These libs are also linked to in packages that depend on this one.
  nativeSharedLibs ? [],
  # Whether to compile each module into a native shared library that is loaded whenever the module is imported in order to accelerate evaluation
  precompileModules ? false,
  # Whether to compile the package into a native shared library that is loaded whenever *any* of the package's modules is imported into another package.
  # If `precompileModules` is also `true`, the latter only affects imports within the current package.
  precompilePackage ? precompileModules,
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
  mkSharedLib = name: args: runBareCommand "${name}-dynlib" {
    buildInputs = [ stdenv.cc ] ++ lib.optional stdenv.isDarwin darwin.cctools;
    libName = "${name}${stdenv.hostPlatform.extensions.sharedLibrary}";
  } ''
    mkdir -p $out
    ${leanc}/bin/leanc -fPIC -shared ${lib.optionalString stdenv.isLinux "-Bsymbolic"} ${lib.optionalString stdenv.isDarwin "-Wl,-undefined,dynamic_lookup"} -L ${gmp}/lib \
      ${args} -o $out/$libName
  '';
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
  allExternalDeps = lib.unique (lib.foldr (dep: allExternalDeps: allExternalDeps ++ [ dep ] ++ dep.allExternalDeps) [] deps);
  allNativeSharedLibs =
    lib.unique (lib.flatten (nativeSharedLibs ++ (map (dep: dep.allNativeSharedLibs or []) allExternalDeps)));

  # A flattened list of all static library dependencies: this and every dep module's explicitly provided `staticLibDeps`, 
  # plus every dep module itself: `dep.staticLib`
  allStaticLibDeps = 
    lib.unique (lib.flatten (staticLibDeps ++ (map (dep: [dep.staticLib] ++ dep.staticLibDeps or []) allExternalDeps)));

  pathOfSharedLib = dep: dep.libPath or "${dep}/${dep.libName or dep.name}";

  leanPluginFlags = lib.concatStringsSep " " (map (dep: "--plugin=${pathOfSharedLib dep}") pluginDeps);
  loadDynlibsOfDeps = deps: lib.unique (concatMap (d: d.propagatedLoadDynlibs) deps);

  fakeDepRoot = runBareCommandLocal "${name}-dep-root" {} ''
    mkdir $out
    cd $out
    mkdir ${lib.concatStringsSep " " ([name] ++ (map (d: d.name) allExternalDeps))}
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
  # build module (.olean and .c) given derivations of all (immediate) dependencies
  buildMod = mod: deps: mkBareDerivation rec {
    name = "${mod}";
    LEAN_PATH = depRoot mod deps;
    relpath = modToPath mod;
    buildInputs = [ lean ];
    leanPath = relpath + ".lean";
    src = srcRoot + ("/" + leanPath);
    outputs = [ "out" "ilean" "c" ];
    oleanPath = relpath + ".olean";
    ileanPath = relpath + ".ilean";
    cPath = relpath + ".c";
    inherit leanFlags leanPluginFlags;
    leanLoadDynlibFlags = map (p: "--load-dynlib=${pathOfSharedLib p}") (loadDynlibsOfDeps deps);
    buildCommand = ''
      dir=$(dirname $relpath)
      mkdir -p $dir $out/$dir $ilean/$dir $c/$dir
      cp $src $leanPath
      lean -o $out/$oleanPath -i $ilean/$ileanPath -c $c/$cPath $leanPath $leanFlags $leanPluginFlags $leanLoadDynlibFlags
    '';
  } // {
    inherit deps;
    propagatedLoadDynlibs = loadDynlibsOfDeps deps;
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
      leanc -c -o $out/$oPath $leancFlags -fPIC ${if debug then "${drv.c}/${drv.cPath} -g" else "src.c -O3 -DNDEBUG"}
    '';
  };
  mkMod = mod: deps:
    let drv = buildMod mod deps;
        obj = compileMod mod drv;
        # this attribute will only be used if any dependent module is precompiled
        sharedLib = mkSharedLib mod "${obj}/${obj.oPath} ${lib.concatStringsSep " " (map (d: pathOfSharedLib d.sharedLib) deps)}";
    in drv // {
      inherit obj sharedLib;
    } // lib.optionalAttrs precompileModules {
      propagatedLoadDynlibs = [sharedLib];
    };
  externalModMap = lib.foldr (dep: depMap: depMap // dep.mods) {} allExternalDeps;
  # Recursively build `mod` and its dependencies. `modMap` maps module names to
  # `{ deps, drv }` pairs of a derivation and its transitive dependencies (as a nested
  # mapping from module names to derivations). It is passed linearly through the
  # recursion to memoize common dependencies.
  buildModAndDeps = mod: modMap: if modMap ? ${mod} || externalModMap ? ${mod} then modMap else
    let
      deps = filter (p: p != "") (lib.splitString "\n" (readFile (leanDeps mod)));
      modMap' = lib.foldr buildModAndDeps modMap deps;
    in modMap' // { ${mod} = mkMod mod (map (dep: if modMap' ? ${dep} then modMap'.${dep} else externalModMap.${dep}) deps); };
  makeEmacsWrapper = name: lean: writeShellScriptBin name ''
    ${lean-emacs}/bin/emacs --eval "(progn (setq lean4-rootdir \"${lean}\"))" "$@"
  '';
  makeVSCodeWrapper = name: lean: writeShellScriptBin name ''
    PATH=${lean}/bin:$PATH ${lean-vscode}/bin/code "$@"
  '';
  printPaths = deps: writeShellScriptBin "print-paths" ''
    echo '${toJSON {
      oleanPath = [(depRoot "print-paths" deps)];
      srcPath = ["."] ++ map (dep: dep.src) allExternalDeps;
      loadDynlibPaths = map pathOfSharedLib (loadDynlibsOfDeps deps);
    }}'
  '';
  makePrintPathsFor = deps: mods: printPaths deps // mapAttrs (_: mod: makePrintPathsFor (deps ++ [mod]) mods) mods;
  mods' = buildModAndDeps name {};
  allLinkFlags = lib.foldr (shared: acc: acc ++ [ "-L${shared}" "-l${shared.linkName or shared.name}" ]) linkFlags allNativeSharedLibs;

  objects   = mapAttrs (_: m: m.obj) mods';
  staticLib = runCommand "${name}-lib" { buildInputs = [ stdenv.cc.bintools.bintools ]; } ''
    mkdir -p $out
    ar Trcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/${drv.oPath}") (attrValues objects))};
  '';

  # Static lib inputs
  staticLibLinkWrapper = libs: if groupStaticLibs && !stdenv.isDarwin
    then "-Wl,--start-group ${libs} -Wl,--end-group"
    else "${libs}";
  staticLibArguments = staticLibLinkWrapper ("${staticLib}/* ${lib.concatStringsSep " " (map (d: "${d}/*.a") allStaticLibDeps)}");
in rec {
  inherit name lean deps staticLibDeps allNativeSharedLibs allLinkFlags allExternalDeps print-lean-deps src objects staticLib;
  mods = mapAttrs (_: m:
      m //
      # if neither precompilation option was set but a dependent module wants to be precompiled, default to precompiling this package whole
      lib.optionalAttrs (precompilePackage || !precompileModules) { inherit sharedLib; } //
      lib.optionalAttrs precompilePackage { propagatedLoadDynlibs = [sharedLib]; })
    mods';
  modRoot   = depRoot name [ mods.${name} ];
  cTree     = symlinkJoin { name = "${name}-cTree"; paths = map (mod: mod.c) (attrValues mods); };
  oTree     = symlinkJoin { name = "${name}-oTree"; paths = (attrValues objects); };
  iTree     = symlinkJoin { name = "${name}-iTree"; paths = map (mod: mod.ilean) (attrValues mods); };
  sharedLib = mkSharedLib name ''
    ${if stdenv.isDarwin then "-Wl,-force_load,${staticLib}/lib${name}.a" else "-Wl,--whole-archive ${staticLib}/lib${name}.a -Wl,--no-whole-archive"} \
    ${lib.concatStringsSep " " (map (d: "${d.sharedLib}/*") deps)}'';
  executable = runCommand executableName { buildInputs = [ stdenv.cc leanc ]; } ''
    mkdir -p $out/bin
    leanc ${staticLibArguments} \
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
    LEAN_PATH=${modRoot}:$LEAN_PATH LEAN_SRC_PATH=$LEAN_SRC_PATH:${src} exec ${lean-final}/bin/lean "$@"
  '';
  emacs-package = makeEmacsWrapper "emacs-package" lean-package;
  vscode-package = makeVSCodeWrapper "vscode-package" lean-package;

  link-ilean = writeShellScriptBin "link-ilean" ''
    dest=''${1:-.}
    mkdir -p $dest/build/lib
    ln -sf ${iTree}/* $dest/build/lib
  '';

  print-paths = makePrintPathsFor [] (mods' // externalModMap);
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
