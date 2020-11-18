{ debug ? false, stdenv, lib, coreutils, gnused, lean, leanc ? lean, lean-final ? lean, writeScriptBin, bash, lean-emacs, nix, substituteAll }:
with builtins; let
  # "Init.Core" ~> "Init/Core.lean"
  modToLean = mod: replaceStrings ["."] ["/"] mod + ".lean";
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
in
  { name, src, srcDir ? "", deps }: let
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
    #${lean}/bin/lean --deps ${src}/${modToLean mod} | sed -n "s!$LEAN_PATH/!!;\!^${name}/!{s!/!.!g;s!.olean!!;p}" > $out
    # build module (.olean and .c) given derivations of all (transitive) dependencies
    buildMod = mod: deps: let relpath = modToLean mod; in mkDerivation {
      name = "${mod}";
      LEAN_PATH = depRoot mod deps;
      inherit relpath;
      buildInputs = [ lean ];
      outputs = [ "out" "c" ];
      src = src + ("/" + relpath);
      buildCommand = ''
        mkdir -p $(dirname $relpath) $out/$(dirname $relpath) $c
        cp $src $relpath
        lean -o $out/''${relpath%.lean}.olean -c $c/out.c $relpath
      '';
    } // {
      inherit deps;
    };
    compileMod = mod: drv: mkDerivation {
      name = "${mod}-cc";
      buildInputs = [ leanc ];
      src = "${drv.c}/out.c";
      hardeningDisable = [ "all" ];
      buildCommand = ''
        mkdir -p $out
        ln -s $src out.c
        leanc -c -o $out/out.o out.c ${if debug then "-g" else "-O3 -DNDEBUG"}
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
    staticLib = runCommand "${name}-lib" { buildInputs = [ stdenv.cc.bintools.bintools ]; } ''
      mkdir $out
      ar rcs $out/lib${name}.a ${lib.concatStringsSep " " (map (drv: "${drv}/out.o") (attrValues objects))}
    '';
    lean-package = writeScriptBin "lean" ''
      #!${bash}/bin/bash
      set -euo pipefail
      LEAN_PATH=${modRoot} ${lean-final}/bin/lean $@
    '';
    lean-dev = substituteAll {
      name = "lean";
      dir = "bin";
      src = ./lean-dev.in;
      isExecutable = true;
      inherit lean bash nix srcDir;
    };

    emacs-package = writeScriptBin "run-emacs-package" ''
      #!${bash}/bin/bash
      ${lean-emacs}/bin/emacs --eval '(setq lean4-rootdir "${lean-package}")' $@
    '';
    emacs-dev = writeScriptBin "run-emacs-dev" ''
      #!${bash}/bin/bash
      ${lean-emacs}/bin/emacs --eval '(setq lean4-rootdir "${lean-dev}")' $@
    '';
  }
