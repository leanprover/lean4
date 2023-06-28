# Nix Setup

An alternative setup based on Nix provides a perfectly reproducible development environment for your project from the Lean version down to the editor and Lean extension.
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

## Basic Commands

From a Lean shell, run
```bash
$ nix flake new mypkg -t github:leanprover/lean4
```
to create a new Lean package in directory `mypkg` using the latest commit of Lean 4.
Such packages follow the same directory layout as described in the standard setup, except for a `lakefile.lean` replaced by a `flake.nix` file set up so you can run Nix commands on it, for example:
```bash
$ nix build  # build package and all dependencies
$ nix build .#executable  # compile `main` definition into executable (after you've added one)
$ nix run .#emacs-dev  # open a pinned version of Emacs with lean4-mode fully set up
$ nix run .#emacs-dev MyPackage.lean  # arguments can be passed as well, e.g. the file to open
$ nix run .#vscode-dev MyPackage.lean  # ditto, using VS Code
```
Note that if you rename `MyPackage.lean`, you also have to adjust the `name` attribute in `flake.nix` accordingly.
Also note that if you turn the package into a Git repository, only tracked files will be visible to Nix.

As in the standard setup, changes need to be saved to be visible in other files, which have then to be invalidated via an editor command.

If you don't want to or cannot start the pinned editor from Nix, e.g. because you're running Lean inside WSL/a container/on a different machine, you can manually point your editor at the `lean` wrapper script the commands above use internally:
```bash
$ nix build .#lean-dev -o result-lean-dev
```
The resulting `./result-lean-dev/bin/lean` script essentially runs `nix run .#lean` in the current project's root directory when you open a Lean file or use the "refresh dependencies" command such that the correct Lean version for that project is executed.
This includes selecting the correct stage of Lean (which it will compile on the fly, though without progress output) if you are [working on Lean itself](./make/nix.md#editor-integration).

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

Note that the package information in `flake.nix` is currently completely independent from `lakefile.lean` used in the standard setup.
Unifying the two formats is TBD.
