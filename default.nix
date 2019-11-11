{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ? pkgs.llvmPackages_9 }:

# always use clang inside ccache
let stdenv = pkgs.overrideCC pkgs.stdenv (pkgs.ccacheWrapper.override { cc = llvmPackages.clang; });
in pkgs.callPackage ./nix/derivation.nix { inherit llvmPackages stdenv; }
