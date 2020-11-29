{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.temci = {
    url = github:parttimenerd/temci;
    flake = false;
  };
  inputs.nix.url = github:NixOS/nix;
  inputs.mdBook = {
    url = github:leanprover/mdBook;
    flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, temci, nix, mdBook }: flake-utils.lib.eachDefaultSystem (system:
    let
      packages = nixpkgs.legacyPackages.${system}.callPackage (./nix/packages.nix) { inherit nix temci mdBook; };
    in {
      packages = packages // rec {
        debug = packages.override { debug = true; };
        sanitized = packages.override { extraCMakeFlags = [ "-DLEAN_EXTRA_CXX_FLAGS=-fsanitize=address,undefined" "-DLEANC_EXTRA_FLAGS=-fsanitize=address,undefined" "-DSMALL_ALLOCATOR=OFF" ]; };
        sandebug = sanitized.override { debug = true; };
        tsan = packages.override {
          extraCMakeFlags = [ "-DLEAN_EXTRA_CXX_FLAGS=-fsanitize=thread" "-DLEANC_EXTRA_FLAGS=-fsanitize=thread" "-DCOMPRESSED_OBJECT_HEADER=OFF" ];
          stage0 = (packages.override {
            # Compressed headers currently trigger data race reports in tsan.
            # Turn them off for stage 0 as well so stage 1 can read its own stdlib.
            extraCMakeFlags = [ "-DCOMPRESSED_OBJECT_HEADER=OFF" ];
          }).stage1;
        };
        tsandebug = tsan.override { debug = true; };
      };

      defaultPackage = packages.lean;

      checks.lean = packages.test;
    }) // rec {
      templates.pkg = {
        path = ./nix/templates/pkg;
        description = "A custom Lean package";
      };

      defaultTemplate = templates.pkg;
    };
}
