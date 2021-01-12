# Setting Up Lean

There are currently two ways to set up a Lean 4 development environment:

* [basic setup](./setup.md#basic-setup) (Linux/macOS/Windows): uses [`elan`](https://github.com/Kha/elan) + your preinstalled editor
* [Nix setup](./setup.md#nix-setup) (Linux/macOS/WSL): uses the [Nix](https://nixos.org/nix/) package manager for installing all dependencies localized to your project

## Basic Setup

Release builds for all supported platforms are available at <https://github.com/leanprover/lean4/releases>.
Instead of downloading these and setting up the paths manually, however, it is recommended to use the Lean version manager [`elan`](https://github.com/Kha/elan) instead:
```sh
$ elan self update  # in case you haven't updated elan in a while
# download & activate latest Lean 4 release (https://github.com/leanprover/lean4/releases)
$ elan default leanprover/lean4:stable
# alternatively, use the latest nightly build (https://github.com/leanprover/lean4-nightly/releases)
$ elan default leanprover/lean4:nightly
# alternatively, activate Lean 4 in current directory only
$ elan override leanprover/lean4:stable
```

Lean 4 comes with a basic package manager `leanpkg` that mostly works [as in Lean 3](https://leanprover.github.io/reference/using_lean.html#using-the-package-manager).
Note however that it currently depends on `make` (and `sh`) for recursive compilation.
It has been tested on Windows by installing these tools using [MSYS2](https://www.msys2.org/), but [MinGW](http://www.mingw.org/) or WSL should work, too.

Lean implements the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) that can be used for interactive development in [Emacs](https://github.com/leanprover/lean4/tree/master/lean4-mode/README.md), [VS Code](https://github.com/mhuisi/vscode-lean4), and possibly other editors.

Changes must be saved to be visible in other files, which must then be invalidated using an editor command (see links above).

## Nix Setup

The alternative setup based on Nix provides a perfectly reproducible development environment for your project from the Lean version down to the editor and Lean extension.
However, it is still experimental and subject to change; in particular, it is heavily based on an unreleased version of Nix enabling [Nix Flakes](https://www.tweag.io/blog/2020-05-25-flakes/). The setup has been tested on NixOS, other Linux distributions, and macOS.

After installing (any version of) Nix (<https://nixos.org/download.html>), you can easily open a shell with the particular pre-release version of Nix needed by and tested with our setup (called the "Lean shell" from here on):
```bash
$ nix-shell https://github.com/leanprover/lean4/archive/master.tar.gz -A nix
```
While this shell is sufficient for executing the steps below, it is recommended to also set the following options in `/etc/nix/nix.conf` (`nix.extraOptions` in NixOS):
```
max-jobs = auto  # Allow building multiple derivations in parallel
keep-outputs = true  # Do not garbage-collect build time-only dependencies (e.g. clang)
# Allow fetching build results from the Lean Cachix cache
trusted-substituters = https://lean4.cachix.org/
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= lean4.cachix.org-1:mawtxSxcaiWE24xCXXgh3qnvlTkyU7evRRnGeAhD4Wk=
```
On a multi-user installation of Nix (the default), you need to restart the Nix daemon afterwards:
```bash
sudo pkill nix-daemon
```

The [Cachix](https://cachix.org/) integration will magically beam any build steps already executed by the CI right onto your machine when calling Nix commands in the shell opened above.
It can be set up analogously as a cache for your own project.

Note: Your system Nix might print warnings about not knowing some of the settings used by the Lean shell Nix, which can be ignored.

### Basic Commands

From a Lean shell, run
```bash
$ nix flake new mypkg -t github:leanprover/lean4
```
to create a new Lean package in directory `mypkg` using the latest commit of Lean 4.
The Lean package comes with a package root file `MyPackage.lean` and a `flake.nix` set up so you can run Nix commands on it, for example:
```bash
$ nix build  # build package and all dependencies
$ nix build .#executable  # compile `main` definition into executable
$ nix run .#emacs-dev  # open a pinned version of Emacs with lean4-mode fully set up
$ nix run .#emacs-dev MyPackage.lean  # arguments can be passed as well, e.g. the file to open
$ nix run .#vscode-dev MyPackage.lean  # ditto, using VS Code
```
Note that if you rename `MyPackage.lean`, you also have to adjust the `name` attribute in `flake.nix` accordingly.

There is preliminary integration of the Nix-based build system into editors started as above, which automatically builds dependencies when opening or invalidating a file.
There is no progress report yet, and build errors from dependencies will crash the language server; see the stderr logs for the build error in that case.

Package dependencies can be added as further input flakes and passed to the `deps` list of `buildLeanPackage`. Example: <https://github.com/Kha/testpkg2/blob/master/flake.nix#L5>

For hacking, it can be useful to temporarily override an input with a local checkout/different version of a dependency:
```bash
$ nix build --override-input somedep path/to/somedep
```

On a build error, Nix will show the last 10 lines of the output by default. You can pass `-L` to `nix build` to show all lines, or pass the shown `*.drv` path to `nix log` to show the full log after the fact.

Keeping all outputs ever built on a machine alive can accumulate to quite impressive amounts of disk space, so you might want to trigger the Nix GC when `/nix/store/` has grown too large:
```bash
nix-collect-garbage
```
This will remove everything not reachable from "GC roots" such as the `./result` symlink created by `nix build`.

Note that the package information in `flake.nix` is currently completely independent from `leanpkg.toml` used in the basic setup.
Unifying the two formats is TBD.
