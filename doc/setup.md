# Supported Platforms

### Tier 1

Platforms built & tested by our CI, available as nightly & stable releases via elan (see above)

* x86-64 Linux with glibc 2.27+
* x86-64 macOS 10.15+
* x86-64 Windows 10+

### Tier 2

Platforms cross-compiled but not tested by our CI, available as nightly & stable releases

Releases may be silently broken due to the lack of automated testing.
Issue reports and fixes are welcome.

* aarch64 Linux with glibc 2.27+

### Tier 3

Platforms that are known to work from manual testing, but do not come with CI or official releases

* aarch64 (M1) macOS - may also [use x86-64 releases via Rosetta](https://github.com/leanprover/elan#manual-installation)

# Setting Up Lean

There are currently two ways to set up a Lean 4 development environment:

* [basic setup](./setup.md#basic-setup) (Linux/macOS/Windows): uses [`elan`](https://github.com/leanprover/elan) + your preinstalled editor
* [Nix setup](./setup.md#nix-setup) (Linux/macOS/WSL): uses the [Nix](https://nixos.org/nix/) package manager for installing all dependencies localized to your project

See also the [quickstart](./quickstart.md) instructions for using the basic setup with VS Code as the editor.

## Basic Setup

Release builds for all supported platforms are available at <https://github.com/leanprover/lean4/releases>.
Instead of downloading these and setting up the paths manually, however, it is recommended to use the Lean version manager [`elan`](https://github.com/leanprover/elan) instead:
```sh
$ elan self update  # in case you haven't updated elan in a while
# download & activate latest Lean 4 release (https://github.com/leanprover/lean4/releases)
$ elan default leanprover/lean4:stable
# alternatively, use the latest nightly build (https://github.com/leanprover/lean4-nightly/releases)
$ elan default leanprover/lean4:nightly
# alternatively, activate Lean 4 in current directory only
$ elan override set leanprover/lean4:stable
```

### `lake`

Lean 4 comes with a package manager named `lake`.
Use `lake init foo` to initialize a Lean package `foo` in the current directory, and `lake build` to typecheck and build it as well as all its dependencies. Use `lake help` to learn about further commands.
The general directory structure of a package `foo` is
```sh
lakefile.lean  # package configuration
lean-toolchain # specifies the lean version to use
Foo.lean       # main file, import via `import Foo`
Foo/
  A.lean       # further files, import via e.g. `import Foo.A`
  A/...        # further nesting
build/         # `lake` build output directory
```

After running `lake build` you will see a binary named `./build/bin/foo` and when you run it you should see the output:
```
Hello, world!
```

### Editing

Lean implements the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) that can be used for interactive development in [Emacs](https://github.com/leanprover/lean4-mode), [VS Code](https://github.com/leanprover-community/vscode-lean4), and possibly other editors.

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
Such packages follow the same directory layout as described in the basic setup above, except for a `lakefile.lean` replaced by a `flake.nix` file set up so you can run Nix commands on it, for example:
```bash
$ nix build  # build package and all dependencies
$ nix build .#executable  # compile `main` definition into executable (after you've added one)
$ nix run .#emacs-dev  # open a pinned version of Emacs with lean4-mode fully set up
$ nix run .#emacs-dev MyPackage.lean  # arguments can be passed as well, e.g. the file to open
$ nix run .#vscode-dev MyPackage.lean  # ditto, using VS Code
```
Note that if you rename `MyPackage.lean`, you also have to adjust the `name` attribute in `flake.nix` accordingly.
Also note that if you turn the package into a Git repository, only tracked files will be visible to Nix.

As in the basic setup, changes need to be saved to be visible in other files, which have then to be invalidated via an editor command.

If you don't want to or cannot start the pinned editor from Nix, e.g. because you're running Lean inside WSL/a container/on a different machine, you can manually point your editor at the `lean` wrapper script the commands above use internally:
```bash
$ nix build .#lean-dev -o result-lean-dev
```
The resulting `./result-lean-dev/bin/lean` script essentially runs `nix run .#lean` in the current project's root directory when you open a Lean file or use the "refresh dependencies" command such that the correct Lean version for that project is executed.
This includes selecting the correct stage of Lean (which it will compile on the fly, though without progress output) if you are [working on Lean itself](../make/nix.md#editor-integration).

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

Note that the package information in `flake.nix` is currently completely independent from `lakefile.lean` used in the basic setup.
Unifying the two formats is TBD.
