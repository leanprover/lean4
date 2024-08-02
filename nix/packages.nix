{ src, pkgs, ... } @ args:
with pkgs;
let
  # https://github.com/NixOS/nixpkgs/issues/130963
  llvmPackages = if stdenv.isDarwin then llvmPackages_11 else llvmPackages_15;
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
    inherit src buildLeanPackage llvmPackages;
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
  }));
in {
  inherit cc buildLeanPackage llvmPackages;
  nixpkgs = pkgs;
  ciShell = writeShellScriptBin "ciShell" ''
    set -o pipefail
    export PATH=${moreutils}/bin:$PATH
    # prefix lines with cumulative and individual execution time
    "$@" |& ts -i "(%.S)]" | ts -s "[%M:%S"
  '';
} // lean.stage1
