{
  description = "Lean interactive theorem prover";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;

  outputs = { self, nixpkgs }: {

    packages.x86_64-linux.lean =
      with import nixpkgs { system = "x86_64-linux"; };
      let cc = ccacheWrapper.override rec {
            cc = llvmPackages_10.clang;
            extraConfig = ''
export CCACHE_DIR=/var/cache/ccache
export CCACHE_UMASK=007
export CCACHE_BASE_DIR=$NIX_BUILD_TOP
[ -d $CCACHE_DIR ] || exec ${cc}/bin/$(basename "$0") "$@"
          '';
          };
          lean = callPackage (import ./new.nix) {
            stdenv = overrideCC stdenv cc;
          };
      in lean.stage1 // lean;

    defaultPackage.x86_64-linux = self.packages.x86_64-linux.lean;

  };
}
