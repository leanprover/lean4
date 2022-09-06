{
  description = "Lean documentation";

  inputs.lean.url = path:../.;
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.mdBook = {
    url = github:leanprover/mdBook;
    flake = false;
  };
  inputs.alectryon = {
    url = github:Kha/alectryon/typeid;
    flake = false;
  };
  inputs.leanInk = {
    url = github:leanprover/LeanInk;
    flake = false;
  };

  outputs = inputs@{ self, ... }: inputs.flake-utils.lib.eachDefaultSystem (system:
    with inputs.lean.packages.${system}; with nixpkgs;
    let
      doc-src = lib.sourceByRegex ../. ["doc.*" "tests(/lean(/beginEndAsMacro.lean)?)?"];
    in {
    packages = rec {
      lean-mdbook = mdbook.overrideAttrs (drv: rec {
        name = "lean-${mdbook.name}";
        src = inputs.mdBook;
        cargoDeps = drv.cargoDeps.overrideAttrs (_: {
          inherit src;
          outputHash = "sha256-mhTWHs/bsmm3FH59SkUxBTl5lEH2Rlz/aF9CuBTu1TE=";
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
          cp -r ${inked}/* .
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
        name = "Main";
        src = inputs.leanInk;
        deps = [ (buildLeanPackage {
          name = "LeanInk";
          src = inputs.leanInk;
        }) ];
        executableName = "leanInk";
        linkFlags = ["-rdynamic"];
      }).executable;
      alectryon = python3Packages.buildPythonApplication {
        name = "alectryon";
        src = inputs.alectryon;
        propagatedBuildInputs =
          [ leanInk lean-all ] ++
          # https://github.com/cpitclaudel/alectryon/blob/master/setup.cfg
          (with python3Packages; [ pygments dominate beautifulsoup4 docutils ]);
        doCheck = false;
      };
      renderLean = name: file: runCommandNoCC "${name}.md" { buildInputs = [ alectryon ]; } ''
        mkdir -p $(basename $out/${name})
        alectryon --frontend lean4+markup ${file} --backend webpage -o $out/${name}.md
      '';
      listFilesRecursiveRel = root: dir: lib.flatten (lib.mapAttrsToList (name: type:
        if type == "directory" then
          listFilesRecursiveRel root ("${dir}/${name}")
        else
          dir + "/${name}"
      ) (builtins.readDir "${root}/${dir}"));
      renderDir = dir: let
        inputs = builtins.filter (n: builtins.match ".*\.lean" n != null) (listFilesRecursiveRel dir ".");
        outputs = lib.genAttrs inputs (n: renderLean n "${dir}/${n}");
      in
        outputs // symlinkJoin { inherit name; paths = lib.attrValues outputs; };
      inked = renderDir ./.;
      doc = book;
    };
    defaultPackage = self.packages.${system}.doc;
  });
}
