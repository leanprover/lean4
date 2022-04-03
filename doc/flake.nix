{
  description = "Lean documentation";

  inputs.lean.url = path:../.;
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.mdBook = {
    url = github:leanprover/mdBook;
    flake = false;
  };
  inputs.alectryon-src = {
    url = github:Kha/alectryon/typeid;
    flake = false;
  };
  inputs.leanInk-src = {
    url = github:leanprover/LeanInk;
    flake = false;
  };

  outputs = { self, lean, flake-utils, mdBook, alectryon-src, leanInk-src }: flake-utils.lib.eachDefaultSystem (system:
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
      book = stdenv.mkDerivation {
        name ="lean-doc";
        src = doc-src;
        buildInputs = [ lean-mdbook ];
        buildCommand = ''
          mkdir $out
          # necessary for `additional-css`...?
          cp -r --no-preserve=mode $src/doc/* .
          # overwrite stub .lean.md files
          cp -r ${examples}/* .
          mdbook build -d $out
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
      leanInk = (buildLeanPackage {
        name = "LeanInk";
        src = leanInk-src;
        executableName = "leanInk";
        linkFlags = ["-rdynamic"];
      }).executable;
      alectryon = python3Packages.buildPythonApplication {
        name = "alectryon";
        src = alectryon-src;
        propagatedBuildInputs =
          [ leanInk lean-all ] ++
          # https://github.com/cpitclaudel/alectryon/blob/master/setup.cfg
          (with python3Packages; [ pygments dominate beautifulsoup4 docutils ]);
        doCheck = false;
      };
      examples = let
        renderLean = name: file: runCommandNoCC "${name}.md" { buildInputs = [ alectryon ]; } ''
          mkdir -p $out/examples
          alectryon --frontend lean4+markup ${file} --backend webpage -o $out/examples/${name}.md
        '';
        ents = builtins.readDir ./examples;
        inputs = lib.filterAttrs (n: t: builtins.match ".*\.lean" n != null && t == "regular") ents;
        outputs = lib.mapAttrs (n: _: renderLean n ./examples/${n}) inputs;
      in
        outputs // symlinkJoin { name = "examples"; paths = lib.attrValues outputs; };
      doc = book;
    };
    defaultPackage = self.packages.${system}.doc;
  });
}
