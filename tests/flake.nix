{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  inputs.lakeprof.url = "github:Kha/lakeprof";
  inputs.lakeprof.inputs.nixpkgs.follows = "nixpkgs";

  outputs =
    inputs:
    let
      lib = inputs.nixpkgs.lib;
      forAllSystems = lib.genAttrs lib.systems.flakeExposed;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = inputs.nixpkgs.legacyPackages.${system};
          lakeprof = inputs.lakeprof.packages.${system}.lakeprof;
        in
        {
          default = pkgs.mkShellNoCC {
            packages = [ lakeprof ] ++ lib.optional pkgs.stdenv.isLinux pkgs.perf;
          };
        }
      );
    };
}
