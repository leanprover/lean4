{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ? pkgs.llvmPackages_8 }:

pkgs.callPackage ./nix/derivation.nix { inherit llvmPackages; }
