{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ? pkgs.llvmPackages_latest }:

pkgs.callPackage ./nix/derivation.nix { inherit llvmPackages; }
