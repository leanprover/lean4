{ pkgs, nix, temci, mdBook, ... } @ args:
with pkgs;
let
  nix-pinned = writeShellScriptBin "nix" ''
    ${nix.defaultPackage.${system}}/bin/nix --experimental-features 'nix-command flakes' --extra-substituters https://lean4.cachix.org/ --option warn-dirty false "$@"
  '';
  llvmPackages = llvmPackages_10;
  cc = ccacheWrapper.override rec {
    # macOS doesn't like the lld override, but I guess it already uses that anyway
    cc = if system == "x86_64-darwin" then llvmPackages.clang else llvmPackages.clang.override {
      # linker go brrr
      bintools = llvmPackages.lldClang.bintools;
    };
    extraConfig = ''
      export CCACHE_DIR=/nix/var/cache/ccache
      export CCACHE_UMASK=007
      export CCACHE_BASE_DIR=$NIX_BUILD_TOP
      [ -d $CCACHE_DIR ] || exec ${cc}/bin/$(basename "$0") "$@"
    '';
  };
  lean = callPackage (import ./bootstrap.nix) (args // {
    stdenv = overrideCC llvmPackages.stdenv cc;
    inherit buildLeanPackage;
  });
  makeOverridableLeanPackage = f:
    let newF = origArgs: f origArgs // {
      overrideArgs = newArgs: makeOverridableLeanPackage f (origArgs // newArgs);
    };
    in lib.setFunctionArgs newF (lib.getFunctionArgs f) // {
      override = args: makeOverridableLeanPackage (f.override args);
    };
  buildLeanPackage = makeOverridableLeanPackage (callPackage (import ./buildLeanPackage.nix) (args // {
    inherit (lean) stdenv leanc;
    lean = lean.stage1;
    inherit lean-emacs;
    nix = nix-pinned;
  }));
  lean4-mode = emacsPackages.melpaBuild {
    pname = "lean4-mode";
    version = "1";
    src = ../lean4-mode;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ dash dash-functional f flycheck lsp-mode s ];
    recipe = pkgs.writeText "recipe" ''
      (lean4-mode :repo "leanprover/lean4" :fetcher github :files ("*.el"))
    '';
    fileSpecs = [ "*.el" ];
  };
  lean-emacs = emacsWithPackages [ lean4-mode ];
  lean-mdbook = mdbook.overrideAttrs (drv: rec {
    name = "lean-${mdbook.name}";
    src = mdBook;
    cargoDeps = drv.cargoDeps.overrideAttrs (_: {
      inherit src;
      outputHash = "sha256-BTm76YxY/tI4Pg53UbR+7KiQydb9L0FGYNZ0UKGyacw=";
    });
    doCheck = false;
  });
  doc = stdenv.mkDerivation {
    name ="lean-doc";
    src = ../.;
    buildInputs = [ lean-mdbook ];
    buildCommand = ''
      mdbook build -d $out $src/doc
    '';
  };
  # We use a separate derivation instead of `checkPhase` so we can push it but not `doc` to the binary cache
  doc-test = stdenv.mkDerivation {
    name ="lean-doc-test";
    src = ../.;
    buildInputs = [ lean-mdbook lean.stage1 strace ];
    patchPhase = ''
      cd doc
      patchShebangs test
    '';
    buildPhase = ''
      mdbook test
      touch $out
    '';
    dontInstall = true;
  };
in {
  inherit cc lean4-mode buildLeanPackage llvmPackages;
  lean = lean.stage1;
  stage0check-mod = (lean.stage1.Lean.overrideArgs { lean-final = lean.stage0; }).check-mod;
  HEAD-as-stage0 = (lean.stage1.Lean.overrideArgs { srcCheckTarget = "$root#stage0-from-input.stage0check-mod"; srcCheckArgs = "(--override-input lean-stage0 $root\?rev=$(git rev-parse HEAD) -- -Dinterpreter.prefer_native=false \"$@\")"; });
  HEAD-as-stage1 = (lean.stage1.Lean.overrideArgs { srcCheckTarget = "$root\?rev=$(git rev-parse HEAD)#stage0check-mod"; });
  temci = (import temci {}).override { doCheck = false; };
  nix = nix-pinned;
  nixpkgs = pkgs;
  ciShell = writeShellScriptBin "ciShell" ''
    set -o pipefail
    export PATH=${nix-pinned}/bin:${moreutils}/bin:$PATH
    # prefix lines with cumulative and individual execution time
    "$@" |& ts -i "(%.S)]" | ts -s "[%M:%S"
  '';
  mdbook = lean-mdbook;
  inherit doc doc-test;
} // lean.stage1.Lean // lean.stage1 // lean
