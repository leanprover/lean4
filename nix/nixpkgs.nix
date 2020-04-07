import (builtins.fetchTarball {
  name = "nixpkgs-unstable-2020-04-08";
  # Commit hash from `git ls-remote https://github.com/nixos/nixpkgs-channels nixpgs-unstable`
  url = https://github.com/nixos/nixpkgs/archive/40dcac87f4afb452f7882c6102eded87169a6134.tar.gz;
  # Hash obtained using `nix-prefetch-url --unpack <url>`
  sha256 = "0x2zmh8mz6bi7cxx62macmyan4cdxplnpvfm50fmhrp34a2scbm3";
}) {}
