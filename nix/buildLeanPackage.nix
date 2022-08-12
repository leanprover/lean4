{ lean, lean-leanDeps ? lean, lean-final ? lean, leanc,
  stdenv, lib, coreutils, gnused, writeShellScriptBin, bash, lean-emacs, lean-vscode, nix, substituteAll, symlinkJoin, linkFarmFromDrvs,
  runCommand, gmp, darwin, mkShell, ... }:
let lean-final' = lean-final; in
lib.makeOverridable (
{ name, src, fullSrc ? src, srcPrefix ? "",
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
  # Lean modules to include.
  # A set of Lean modules names as strings (`"Foo.Bar"`) or attrsets (`{ name = "Foo.Bar"; glob = "one" | "submodules" | "andSubmodules"; }`);
  # see Lake README for glob meanings. Dependencies of selected modules are always included.
  roots ? [ name ],
  # Output from `lean --deps-json` on package source files. Persist the corresponding output attribute to a file and pass it back in here to avoid IFD.
  # Must be refreshed on any change in `import`s or set of source file names.
  modDepsFile ? null,
  # Whether to compile each module into a native shared library that is loaded whenever the module is imported in order to accelerate evaluation
  precompileModules ? false,
  # Whether to compile the package into a native shared library that is loaded whenever *any* of the package's modules is imported into another package.
  # If `precompileModules` is also `true`, the latter only affects imports within the current package.
  precompilePackage ? precompileModules,
  # Lean plugin dependencies. Each derivation `plugin` should contain a plugin library at path `${plugin}/${plugin.name}`.
  pluginDeps ? [],
  debug ? false, leanFlags ? [], leancFlags ? [], linkFlags ? [], executableName ? lib.toLower name, libName ? name,
  srcTarget ? "..#stage0", srcArgs ? "(\${args[*]})", lean-final ? lean-final' }@args:
with builtins; let
  # "Init.Core" ~> "Init/Core"
  modToPath = mod: replaceStrings ["."] ["/"] mod;
  modToAbsPath = mod: "${src}/${modToPath mod}";
  modToLean = mod: "${modToAbsPath mod}.lean";
  bareStdenv = ./bareStdenv;
  mkBareDerivation = args: derivation (args // {
    name = lib.strings.sanitizeDerivationName args.name;
    stdenv = bareStdenv;
    inherit (stdenv) system;
    buildInputs = (args.buildInputs or []) ++ [ coreutils ];
    builder = stdenv.shell;
    args = [ "-c" ''
      source $stdenv/setup
      set -u
      ${args.buildCommand}
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

  # submodules "Init" = ["Init.List.Basic", "Init.Core", ...]
  submodules = mod: let
    dir = readDir (modToAbsPath mod);
    f = p: t:
      if t == "directory" then
        submodules "${mod}.${p}"
      else
        let m = builtins.match "(.*)\.lean" p;
        in lib.optional (m != null) "${mod}.${head m}";
  in concatLists (lib.mapAttrsToList f dir);

  # conservatively approximate list of source files matched by glob
  expandGlobAllApprox = g:
    if typeOf g == "string" then
      # we can't know the required files without parsing dependencies (which is what we want this
      # function for), so we approximate to the entire package.
      let root = (head (split "\\." g));
      in lib.optional (pathExists (modToLean root)) root ++ lib.optionals (pathExists (modToAbsPath root)) (submodules root)
    else if g.glob == "one" then expandGlobAllApprox g.mod
    else if g.glob == "submodules" then submodules g.mod
    else if g.glob == "andSubmodules" then [g.mod] ++ submodules g.mod
    else throw "unknown glob kind '${g}'";
  # list of modules that could potentially be involved in the build
  candidateMods = filter (m: pathExists (modToLean m)) (lib.unique (concatMap expandGlobAllApprox roots));
  candidateFiles = map modToLean candidateMods;
  modDepsFile = args.modDepsFile or mkBareDerivation {
    name = "${name}-deps.json";
    buildCommand = ''
      mkdir $out
      ${lean-leanDeps}/bin/lean --deps-json ${lib.concatStringsSep " " candidateFiles} > $out/$name
    '';
  };
  modDeps = fromJSON (
    # the only possible references to store paths in the JSON should be inside errors, so no chance of missed dependencies from this
    unsafeDiscardStringContext (readFile "${modDepsFile}/${modDepsFile.name}"));
  modDepsMap = listToAttrs (lib.zipListsWith lib.nameValuePair candidateMods modDeps.imports);
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
      deps = if modDepsMap.${mod}.errors == []
             then map (m: m.module) modDepsMap.${mod}.imports
             else abort "errors while parsing imports of ${mod}:\n${lib.concatStringsSep "\n" modDepsMap.${mod}.errors}";
      modMap' = lib.foldr buildModAndDeps modMap deps;
    in modMap' // { ${mod} = mkMod mod (map (dep: if modMap' ? ${dep} then modMap'.${dep} else externalModMap.${dep}) deps); };
  makeEmacsWrapper = name: emacs: lean: writeShellScriptBin name ''
    ${emacs} --eval "(progn (setq lean4-rootdir \"${lean}\"))" "$@"
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
  expandGlob = g:
    if typeOf g == "string" then [g]
    else if g.glob == "one" then [g.mod]
    else if g.glob == "submodules" then submodules g.mod
    else if g.glob == "andSubmodules" then [g] ++ submodules g.mod
    else throw "unknown glob kind '${g}'";
  mods' = lib.foldr buildModAndDeps {} (concatMap expandGlob roots);
  allLinkFlags = lib.foldr (shared: acc: acc ++ [ "-L${shared}" "-l${shared.linkName or shared.name}" ]) linkFlags allNativeSharedLibs;

  objects   = mapAttrs (_: m: m.obj) mods';
  staticLib = runCommand "${name}-lib" { buildInputs = [ stdenv.cc.bintools.bintools ]; } ''
    mkdir -p $out
    ar Trcs $out/lib${libName}.a ${lib.concatStringsSep " " (map (drv: "${drv}/${drv.oPath}") (attrValues objects))};
  '';

  staticLibLinkWrapper = libs: if groupStaticLibs && !stdenv.isDarwin
    then "-Wl,--start-group ${libs} -Wl,--end-group"
    else "${libs}";
in rec {
  inherit name lean deps staticLibDeps allNativeSharedLibs allLinkFlags allExternalDeps src objects staticLib modDepsFile;
  mods = mapAttrs (_: m:
      m //
      # if neither precompilation option was set but a dependent module wants to be precompiled, default to precompiling this package whole
      lib.optionalAttrs (precompilePackage || !precompileModules) { inherit sharedLib; } //
      lib.optionalAttrs precompilePackage { propagatedLoadDynlibs = [sharedLib]; })
    mods';
  modRoot   = depRoot name (attrValues mods);
  cTree     = symlinkJoin { name = "${name}-cTree"; paths = map (mod: mod.c) (attrValues mods); };
  oTree     = symlinkJoin { name = "${name}-oTree"; paths = (attrValues objects); };
  iTree     = symlinkJoin { name = "${name}-iTree"; paths = map (mod: mod.ilean) (attrValues mods); };
  sharedLib = mkSharedLib "lib${libName}" ''
    ${if stdenv.isDarwin then "-Wl,-force_load,${staticLib}/lib${libName}.a" else "-Wl,--whole-archive ${staticLib}/lib${libName}.a -Wl,--no-whole-archive"} \
    ${lib.concatStringsSep " " (map (d: "${d.sharedLib}/*") deps)}'';
  executable = lib.makeOverridable ({ withSharedStdlib ? false }: let
      objPaths = map (drv: "${drv}/${drv.oPath}") (attrValues objects) ++ lib.optional withSharedStdlib "${lean-final.leanshared}/*";
    in runCommand executableName { buildInputs = [ stdenv.cc leanc ]; } ''
      mkdir -p $out/bin
      leanc ${staticLibLinkWrapper (lib.concatStringsSep " " (objPaths ++ map (d: "${d}/*.a") allStaticLibDeps))} \
        -o $out/bin/${executableName} \
        ${lib.concatStringsSep " " allLinkFlags}
    '') {};

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
  emacs-dev = makeEmacsWrapper "emacs-dev" "${lean-emacs}/bin/emacs" lean-dev;
  emacs-path-dev = makeEmacsWrapper "emacs-path-dev" "emacs" lean-dev;
  vscode-dev = makeVSCodeWrapper "vscode-dev" lean-dev;

  devShell = mkShell {
    buildInputs = [ nix ];
    shellHook = ''
      export LEAN_SRC_PATH="$PWD/${srcPrefix}"
    '';
  };
})
