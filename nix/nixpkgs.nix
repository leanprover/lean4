import (builtins.fetchTarball {
  name = "nixpkgs-unstable-2020-04-08";
  # Commit hash from `git ls-remote https://github.com/NixOS/nixpkgs-channels nixpkgs-unstable`
  url = https://github.com/nixos/nixpkgs/archive/3b4df94aeb6e215085d08e3d5b0edc1313b9f584.tar.gz;
  # Hash obtained using `nix-prefetch-url --unpack <url>`
  sha256 = "1z8fnqxi0zd3wmjnmc4l2s4nq812mx0h4r09zdqi5si2in6rksxs";
}) {}
