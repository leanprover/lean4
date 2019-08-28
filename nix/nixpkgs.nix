import (builtins.fetchTarball {
    name = "nixos-unstable-2019-08-28";
    # Commit hash from `git ls-remote https://github.com/nixos/nixpkgs-channels nixos-unstable`
    url = https://github.com/nixos/nixpkgs/archive/3f4144c30a6351dd79b177328ec4dea03e2ce45f.tar.gz;
    # Hash obtained using `nix-prefetch-url --unpack <url>`
    sha256 = "1qg5n60n3fr6cypihnrjw451fadps5pysj5p0vvfb320mpfvlbjb";
  }) {}
