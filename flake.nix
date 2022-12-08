{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.nix.url = github:NixOS/nix;
  inputs.lean4-mode = {
    url = github:leanprover/lean4-mode;
    flake = false;
  };
  # used *only* by `stage0-from-input` below
  #inputs.lean-stage0 = {
  #  url = github:leanprover/lean4;
  #  inputs.nixpkgs.follows = "nixpkgs";
  #  inputs.flake-utils.follows = "flake-utils";
  #  inputs.nix.follows = "nix";
  #  inputs.lean4-mode.follows = "lean4-mode";
  #};

  outputs = { self, nixpkgs, flake-utils, nix, lean4-mode, ... }@inputs: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        inherit system;
        # for `vscode-with-extensions`
        config.allowUnfree = true;
      };
      lean-packages = pkgs.callPackage (./nix/packages.nix) { inherit nix lean4-mode; };
    in {
      packages = lean-packages // rec {
        debug = lean-packages.override { debug = true; };
        stage0debug = lean-packages.override { stage0debug = true; };
        sanitized = lean-packages.override { extraCMakeFlags = [ "-DLEAN_EXTRA_CXX_FLAGS=-fsanitize=address,undefined" "-DLEANC_EXTRA_FLAGS=-fsanitize=address,undefined" "-DSMALL_ALLOCATOR=OFF" "-DSYMBOLIC=OFF" ]; };
        sandebug = sanitized.override { debug = true; };
        tsan = lean-packages.override {
          extraCMakeFlags = [ "-DLEAN_EXTRA_CXX_FLAGS=-fsanitize=thread" "-DLEANC_EXTRA_FLAGS=-fsanitize=thread" "-DCOMPRESSED_OBJECT_HEADER=OFF" ];
          stage0 = (lean-packages.override {
            # Compressed headers currently trigger data race reports in tsan.
            # Turn them off for stage 0 as well so stage 1 can read its own stdlib.
            extraCMakeFlags = [ "-DCOMPRESSED_OBJECT_HEADER=OFF" ];
          }).stage1;
        };
        tsandebug = tsan.override { debug = true; };
        stage0-from-input = lean-packages.override {
          stage0 = pkgs.writeShellScriptBin "lean" ''
            exec ${inputs.lean-stage0.packages.${system}.lean}/bin/lean -Dinterpreter.prefer_native=false "$@"
          '';
        };
        inherit self;
      };
      defaultPackage = lean-packages.lean-all;

      inherit (lean-packages) devShell;

      checks.lean = lean-packages.test;
    }) // rec {
      templates.pkg = {
        path = ./nix/templates/pkg;
        description = "A custom Lean package";
      };

      defaultTemplate = templates.pkg;
    };
}
