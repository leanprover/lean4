# used for `nix-shell https://github.com/leanprover/lean4/archive/master.tar.gz -A nix`
{ nix = (import ./shell.nix {}).nix; } //
(import (
  fetchTarball {
    url = "https://github.com/edolstra/flake-compat/archive/c75e76f80c57784a6734356315b306140646ee84.tar.gz";
    sha256 = "071aal00zp2m9knnhddgr2wqzlx6i6qa1263lv1y7bdn2w20h10h"; }
) {
  src =  ./.;
}).defaultNix
