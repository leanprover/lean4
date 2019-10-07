import (builtins.fetchTarball {
  name = "nixpkgs-unstable-2019-10-07";
  # Commit hash from `git ls-remote https://github.com/nixos/nixpkgs-channels nixos-unstable`
  url = https://github.com/nixos/nixpkgs/archive/795b1555a88627f0739188081527f23259fcc1d2.tar.gz;
  # Hash obtained using `nix-prefetch-url --unpack <url>`
  sha256 = "0lx1snxgankwv18h3jrzz99fmhk036a2gng4xp92c04nx8mcjlgc";
}) {}
