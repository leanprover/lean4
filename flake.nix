{
  description = "Lake (Lean Make) is a new build system and package manager for Lean 4.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-21.05";
    lean = {
      url = "github:leanprover/lean4";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { self
    , flake-utils
    , nixpkgs
    , lean
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      packageName = "Lake";
      src = ./.;
      leanPkgs = lean.packages.${system};
      project = leanPkgs.buildLeanPackage {
        name = packageName;
        inherit src;
      };
      cli = leanPkgs.buildLeanPackage {
        name = "Lake.Main";
        executableName = "lake";
        deps = [ project ];
        linkFlags = pkgs.lib.optional pkgs.stdenv.isLinux "-rdynamic";
        inherit src;
      };
    in
    {
      packages = project // {
        inherit (leanPkgs) lean;

        cli = cli.executable;
      };

      defaultPackage = self.packages.${system}.cli;

      apps.lake = flake-utils.lib.mkApp {
        drv = cli.executable;
      };

      defaultApp = self.apps.${system}.lake;

      inherit (project) devShell;
    });
}
