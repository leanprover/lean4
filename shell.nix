{ pkgs ? import ./nix/nixpkgs.nix, llvmPackages ?pkgs.llvmPackages_9 } @ args:

let attribs = rec {
  lean = import ./default.nix args;
  temci = (import (builtins.fetchGit { url = http://github.com/parttimenerd/temci.git; rev = "4cae802606b871021394e250a280a2154b92f44b"; }) { inherit pkgs; }).override {
    doCheck = false;
  };
  lean4-mode = pkgs.emacsPackages.melpaBuild {
    pname = "lean4-mode";
    version = "1";
    src = ./lean4-mode;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ dash dash-functional f flycheck s ];
    propagatedUserEnvPkgs = [ lean ];
    recipe = pkgs.writeText "recipe" ''
      (lean4-mode :repo "leanprover/lean4" :fetcher github :files ("*.el"))
    '';
    patchPhase = ''
      sed -i 's/lean_wrapped/lean/' *.el
    '';
    fileSpecs = [ "*.el" ];
  };
  emacs = pkgs.emacsWithPackages (epkgs:
    # ???
    with pkgs.emacsPackages.melpaPackages; [ dash dash-functional f flycheck s ] ++ [ lean4-mode ]);
  run-emacs = pkgs.mkShell {
    shellHook = ''
${emacs}/bin/emacs
exit 0
    '';
  };
  shell = pkgs.mkShell.override { stdenv = lean.stdenv; } rec {
    inputsFrom = [ lean ];
    buildInputs = with pkgs; [ temci ccache ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];
    # more convenient `ctest` output
    CTEST_OUTPUT_ON_FAILURE = 1;
  };
};
# use `shell` as default
in attribs.shell // attribs
