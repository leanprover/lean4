{ lean, lean-leanDeps ? lean, lean-final ? lean, leanc,
  stdenv, lib, coreutils, gnused, writeShellScriptBin, bash, lean-emacs, lean-vscode, nix, substituteAll, symlinkJoin, linkFarmFromDrvs,
  ... }:
let lean-final' = lean-final; in
{ name, src, fullSrc ? src, deps ? [ lean.Lean ],
  debug ? false, leanFlags ? [], leancFlags ? [], executableName ? lib.toLower name,
  srcTarget ? "..#stage0", srcArgs ? "(\${args[*]})", lean-final ? lean-final' }:
with builtins; let
  # "Init.Core" ~> "Init/Core"
  modToPath = mod: replaceStrings ["."] ["/"] mod;
  modToLean = mod: modToPath mod + ".lean";
  mkDerivation = args@{ buildCommand, ... }: derivation (args // {
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
  runCommand = name: args: buildCommand: mkDerivation (args // { inherit name buildCommand; });
  runCommandLocal = name: args: buildCommand: runCommand name (args // {
    preferLocalBuild = true;
    allowSubstitutes = false;
  }) buildCommand;
  depRoot = name: deps: mkDerivation {
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
  allDeps = lib.foldr (dep: allDeps: allDeps // { ${dep.name} = dep; } // dep.allDeps) {} deps;
  fakeDepRoot = runCommandLocal "${name}-dep-root" {} ''
    mkdir $out
    cd $out
    mkdir ${lib.concatStringsSep " " ([name] ++ attrNames allDeps)}
  '';
  print-lean-deps = writeShellScriptBin "print-lean-deps" ''
    export LEAN_PATH=${fakeDepRoot}
    ${lean-leanDeps}/bin/lean --deps --stdin | ${gnused}/bin/sed "s!$LEAN_PATH/!!;s!/!.!g;s!.olean!!"
  '';
  # build a file containing the module names of all immediate dependencies of `mod`
  leanDeps = mod: mkDerivation {
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
  buildMod = mod: deps: mkDerivation rec {
    name = "${mod}";
    LEAN_PATH = depRoot mod deps;
    relpath = modToPath mod;
    buildInputs = [ lean ];
    leanPath = relpath + ".lean";
    src = srcRoot + ("/" + leanPath);
    outputs = [ "out" "c" ];
    oleanPath = relpath + ".olean";
    cPath = relpath + ".c";
    inherit leanFlags;
    buildCommand = ''
      mkdir -p $(dirname $relpath) $out/$(dirname $relpath) $c/$(dirname $relpath)
      cp $src $leanPath
      lean -o $out/$oleanPath -c $c/$cPath $leanPath $leanFlags
    '';
  } // {
    inherit deps;
  };
  compileMod = mod: drv: mkDerivation {
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
      leanc -c -o $out/$oPath $leancFlags ${if debug then "${drv.c}/${drv.cPath} -g " else "src.c -O3 -DNDEBUG"}
    '';
  };
  singleton = name: value: listToAttrs [ { inherit name value; } ];
  externalModMap = lib.foldr (dep: depMap: depMap // dep.mods) {} (attrValues allDeps);
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
    ${lean-emacs}/bin/emacs --eval "(progn (setq lean4-rootdir \"${lean}\") (require 'lean4-mode))" "$@"
  '';
  makeVSCodeWrapper = name: lean: writeShellScriptBin name ''
    PATH=${lean}/bin:$PATH ${lean-vscode}/bin/code "$@"
  '';
  printPaths = deps: writeShellScriptBin "print-paths" ''
    echo "${depRoot "print-paths" deps}"
    echo ".:${lib.concatStringsSep ":" (map (dep: dep.src) (attrValues allDeps))}"
  '';
  makePrintPathsFor = deps: mods: printPaths deps // mapAttrs (_: mod: makePrintPathsFor (deps ++ [mod]) mods) mods;
in rec {
  inherit name lean deps allDeps print-lean-deps src;
  mods      = buildModAndDeps name {};
  modRoot   = depRoot name [ mods.${name} ];
  cTree     = symlinkJoin { name = "${name}-cTree"; paths = map (mod: mod.c) (attrValues mods); };
  objects   = mapAttrs compileMod mods;
  oTree     = symlinkJoin { name = "${name}-oTree"; paths = (attrValues objects); };
  staticLib = runCommand "${name}-lib" { buildInputs = [ stdenv.cc.bintools.bintools ]; } ''
    mkdir $out
    ar Trcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/${drv.oPath}") (attrValues objects))}
  '';
  executable = runCommand executableName { buildInputs = [ stdenv.cc ]; } ''
    mkdir -p $out/bin
    ${leanc}/bin/leanc -x none ${staticLib}/* -o $out/bin/${executableName}
  '';

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
  leanpkg-dev = substituteAll {
    name = "leanpkg";
    dir = "bin";
    src = ./leanpkg-dev.in;
    isExecutable = true;
    inherit bash nix srcTarget srcArgs;
    leanpkg = lean;
  };
  lean-dev = symlinkJoin { name = "lean-dev"; paths = [ lean-bin-dev leanpkg-dev ]; };
  emacs-dev = makeEmacsWrapper "emacs-dev" lean-dev;
  vscode-dev = makeVSCodeWrapper "vscode-dev" lean-dev;
}
