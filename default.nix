{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ? pkgs.llvmPackages_9 }:

pkgs.callPackage ./nix/derivation.nix { inherit llvmPackages; }
