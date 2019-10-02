import (builtins.fetchTarball {
    name = "nixos-unstable-2019-10-02";
    # Commit hash from `git ls-remote https://github.com/nixos/nixpkgs-channels nixos-unstable`
    url = https://github.com/nixos/nixpkgs/archive/cbf29876cfc2f81186d2e1e233bf992dfcb07fad.tar.gz;
    # Hash obtained using `nix-prefetch-url --unpack <url>`
    sha256 = "1fvb6dkmcfhrwki0v8wqfr3c8mmhhzqdjnzbcdyw201dx8dj4iqn";
  }) {}
