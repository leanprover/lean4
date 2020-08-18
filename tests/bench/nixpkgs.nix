import (builtins.fetchTarball {
  name = "nixpkgs-unstable-2020-08-18";
  # Commit hash from `git ls-remote https://github.com/NixOS/nixpkgs-channels nixpkgs-unstable`
  url = https://github.com/nixos/nixpkgs/archive/c5815280e92112a25d958a2ec8b3704d7d90c506.tar.gz;
  # Hash obtained using `nix-prefetch-url --unpack <url>`
  sha256 = "09ic4s9s7w3lm0gmcxszm5j20cfv4n5lfvhdvgi7jzdbbbdps1nh";
}) {}
