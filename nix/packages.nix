{ pkgs, nix, temci, mdBook, ... } @ args:
with pkgs;
let
  nix-pinned = writeShellScriptBin "nix" ''
    ${nix.defaultPackage.${system}}/bin/nix --experimental-features 'nix-command flakes' --extra-substituters https://lean4.cachix.org/ --option warn-dirty false "$@"
  '';
  # https://github.com/NixOS/nixpkgs/issues/130963
  llvmPackages = if stdenv.isDarwin then llvmPackages_11 else llvmPackages_12;
  cc = (ccacheWrapper.override rec {
    cc = llvmPackages.clang;
    extraConfig = ''
      export CCACHE_DIR=/nix/var/cache/ccache
      export CCACHE_UMASK=007
      export CCACHE_BASE_DIR=$NIX_BUILD_TOP
      # https://github.com/NixOS/nixpkgs/issues/109033
      args=("$@")
      for ((i=0; i<"''${#args[@]}"; i++)); do
        case ''${args[i]} in
          -frandom-seed=*) unset args[i]; break;;
        esac
      done
      set -- "''${args[@]}"
      [ -d $CCACHE_DIR ] || exec ${cc}/bin/$(basename "$0") "$@"
    '';
  }).overrideAttrs (old: {
    # https://github.com/NixOS/nixpkgs/issues/119779
    installPhase = builtins.replaceStrings ["use_response_file_by_default=1"] ["use_response_file_by_default=0"] old.installPhase;
  });
  stdenv' = if stdenv.isLinux then useGoldLinker stdenv else stdenv;
  lean = callPackage (import ./bootstrap.nix) (args // {
    stdenv = overrideCC stdenv' cc;
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
    inherit (lean) stdenv;
    lean = lean.stage1;
    inherit (lean.stage1) leanc;
    inherit lean-emacs lean-vscode;
    nix = nix-pinned;
  }));
  lean4-mode = emacsPackages.melpaBuild {
    pname = "lean4-mode";
    version = "1";
    commit = "1";
    src = ../lean4-mode;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ dash f flycheck magit-section lsp-mode s ];
    recipe = pkgs.writeText "recipe" ''
      (lean4-mode :repo "leanprover/lean4" :fetcher github :files ("*.el"))
    '';
    fileSpecs = [ "*.el" ];
  };
  lean-emacs = emacsWithPackages [ lean4-mode ];
  # updating might be nicer by building from source from a flake input, but this is good enough for now
  vscode-lean4 = vscode-utils.extensionFromVscodeMarketplace {
      name = "lean4";
      publisher = "leanprover";
      version = "0.0.30";
      sha256 = "sha256-tx0F3COuDT52y7OC9ymxoye5vfgV7Lv/iB6qrzU3/P4=";
  };
  lean-vscode = vscode-with-extensions.override {
    vscodeExtensions = [ vscode-lean4 ];
  };
  lean-mdbook = mdbook.overrideAttrs (drv: rec {
    name = "lean-${mdbook.name}";
    src = mdBook;
    cargoDeps = drv.cargoDeps.overrideAttrs (_: {
      inherit src;
      outputHash = "sha256-GFjy0bkPql/694F3y+mDtUy526IbO3anInVKFeBxlUc=";
    });
    doCheck = false;
  });
  doc-src = lib.sourceByRegex ../. ["doc.*" "tests(/lean(/beginEndAsMacro.lean)?)?"];
  doc = stdenv.mkDerivation {
    name ="lean-doc";
    src = doc-src;
    buildInputs = [ lean-mdbook ];
    buildCommand = ''
      mdbook build -d $out $src/doc
    '';
  };
  # We use a separate derivation instead of `checkPhase` so we can push it but not `doc` to the binary cache
  doc-test = stdenv.mkDerivation {
    name ="lean-doc-test";
    src = doc-src;
    buildInputs = [ lean-mdbook lean.stage1.Leanpkg.lean-package strace ];
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
  inherit cc lean4-mode buildLeanPackage llvmPackages vscode-lean4;
  lean = lean.stage1;
  stage0print-paths = lean.stage1.Leanpkg.print-paths;
  HEAD-as-stage0 = (lean.stage1.Lean.overrideArgs { srcTarget = "..#stage0-from-input.stage0"; srcArgs = "(--override-input lean-stage0 ..\?rev=$(git rev-parse HEAD) -- -Dinterpreter.prefer_native=false \"$@\")"; });
  HEAD-as-stage1 = (lean.stage1.Lean.overrideArgs { srcTarget = "..\?rev=$(git rev-parse HEAD)#stage0"; });
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
  vscode = lean-vscode;
  inherit doc doc-test;
} // lean.stage1.Lean // lean.stage1 // lean
