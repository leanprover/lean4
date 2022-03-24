{
  description = "Lean documentation";

  inputs.lean.url = path:../.;
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.mdBook = {
    url = github:leanprover/mdBook;
    flake = false;
  };

  outputs = { self, lean, flake-utils, mdBook }: flake-utils.lib.eachDefaultSystem (system:
    with lean.packages.${system}; with nixpkgs;
    let
      doc-src = lib.sourceByRegex ../. ["doc.*" "tests(/lean(/beginEndAsMacro.lean)?)?"];
    in {
    packages = rec {
      lean-mdbook = mdbook.overrideAttrs (drv: rec {
        name = "lean-${mdbook.name}";
        src = mdBook;
        cargoDeps = drv.cargoDeps.overrideAttrs (_: {
          inherit src;
          outputHash = "sha256-cPDIcTtUyqwR2ym3JBoHUqStq0TB2YWb9kllv896cFU=";
        });
        doCheck = false;
      });
      doc = stdenv.mkDerivation {
        name ="lean-doc";
        src = doc-src;
        buildInputs = [ lean-mdbook ];
        buildCommand = ''
          mdbook build -d $out $src/doc
        '';
      };
      # We use a separate derivation instead of `checkPhase` so we can push it but not `doc` to the binary cache
      test = stdenv.mkDerivation {
        name ="lean-doc-test";
        src = doc-src;
        buildInputs = [ lean-mdbook stage1.Lean.lean-package strace ];
        patchPhase = ''
          cd doc
          patchShebangs test
        '';
        buildPhase = ''
          mdbook test
          touch $out
        '';
        dontInstall = true;
      };
    };
    defaultPackage = self.packages.${system}.doc;
  });
}
