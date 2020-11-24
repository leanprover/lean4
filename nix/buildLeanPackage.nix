{ debug ? false, stdenv, lib, coreutils, gnused, lean, leanc ? lean, lean-final ? lean, writeShellScriptBin, bash, lean-emacs, nix, substituteAll, symlinkJoin, linkFarmFromDrvs }:
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
in
  { name, src, srcDir ? "", deps }: let
    srcRoot = src;
    fakeDepRoot = runCommandLocal "${name}-dep-root" {} ''
      mkdir $out
      cd $out
      mkdir ${lib.concatStringsSep " " ([name] ++ attrNames deps)}
    '';
    # build a file containing the module names of all immediate dependencies of `mod`
    leanDeps = mod: mkDerivation {
      name ="${mod}-deps";
      src = src + ("/" + modToLean mod);
      buildInputs = [ lean gnused ];
      buildCommand = ''
        export LEAN_PATH=${fakeDepRoot};
        lean --deps $src | sed "s!$LEAN_PATH/!!;s!/!.!g;s!.olean!!" > $out
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
      buildCommand = ''
        mkdir -p $(dirname $relpath) $out/$(dirname $relpath) $c/$(dirname $relpath)
        cp $src $leanPath
        lean -o $out/$oleanPath -c $c/$cPath $leanPath
      '';
    } // {
      inherit deps;
    };
    compileMod = mod: drv: mkDerivation {
      name = "${mod}-cc";
      buildInputs = [ leanc ];
      hardeningDisable = [ "all" ];
      oPath = drv.relpath + ".o";
      buildCommand = ''
        mkdir -p $out/$(dirname ${drv.relpath})
        # make local "copy" so `drv`'s Nix store path doesn't end up in ccache's hash
        ln -s ${drv.c}/${drv.cPath} src.c
        leanc -c -o $out/$oPath src.c ${if debug then "-g" else "-O3 -DNDEBUG"}
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
    makeEmacsWrapper = name: lean: writeShellScriptBin name ''
      ${lean-emacs}/bin/emacs --eval "(progn (setq lean4-rootdir \"${lean}\") (require 'lean4-mode))" $@
    '';
  in rec {
    mods      = buildModAndDeps name (lib.foldr (dep: depMap: depMap // dep.mods) {} (attrValues deps));
    modRoot   = depRoot name [ mods.${name} ];
    objects   = mapAttrs compileMod mods;
    oTree     = symlinkJoin { name = "${name}-oTree"; paths = (attrValues objects); };
    staticLib = runCommand "${name}-lib" { buildInputs = [ stdenv.cc.bintools.bintools ]; } ''
      mkdir $out
      ar Trcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/${drv.oPath}") (attrValues objects))}
    '';

    lean-package = writeShellScriptBin "lean" ''
      LEAN_PATH=${modRoot} ${lean-final}/bin/lean $@
    '';
    emacs-package = makeEmacsWrapper "emacs-package" lean-package;

    lean-dev = substituteAll {
      name = "lean";
      dir = "bin";
      src = ./lean-dev.in;
      isExecutable = true;
      inherit lean bash nix srcDir;
    };
    emacs-dev = makeEmacsWrapper "emacs-dev" lean-dev;
  }
