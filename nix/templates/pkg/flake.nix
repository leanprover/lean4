{
  description = "My Lean package";

  inputs.lean.url = github:leanprover/lean4;
  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, lean, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let leanPkgs = lean.packages.${system}; in rec {
      packages = {
        inherit (leanPkgs) lean;
      } // leanPkgs.buildLeanPackage {
        name = "MyPackage";  # must match the name of the top-level .lean file
        src = ./.;
      };

      defaultPackage = packages.modRoot;
    });
}
