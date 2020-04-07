{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ? pkgs.llvmPackages_10 }:

pkgs.callPackage ./nix/derivation.nix { inherit llvmPackages; }
