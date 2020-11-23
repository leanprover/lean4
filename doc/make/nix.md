While [Nix](https://nixos.org/nix/) can be used to quickly open a shell with all dependencies for the [standard setup](index.md) installed, we also support a setup based purely on Nix, though it is still experimental; in particular, it is heavily based on an unreleased version of Nix enabling [Nix Flakes](https://www.tweag.io/blog/2020-05-25-flakes/). The setup has been tested on NixOS and other Linux distributions.

# Setup

After installing (any version of) Nix ([https://nixos.org/download.html]), you can easily open a shell with the particular pre-release version of Nix needed by and tested with our setup (called the "Lean shell" from here on):
```bash
# in the Lean root directory
$ nix-shell -A nix
```
While this shell is sufficient for executing the steps below, it is recommended to also set the following options in `/etc/nix/nix.conf` (`nix.extraOptions` in NixOS):
```
max-jobs = auto  # Allow building multiple derivations in parallel
keep-outputs = true  # Do not garbage-collect build time-only dependencies (e.g. clang)
extra-sandbox-paths = /nix/var/cache/ccache  # Extra local cache for C/C++ code
# Allow fetching build results from the Lean Cachix cache
extra-trusted-substituters = https://lean4.cachix.org/
extra-trusted-public-keys = lean4.cachix.org-1:mawtxSxcaiWE24xCXXgh3qnvlTkyU7evRRnGeAhD4Wk=
```
The [Cachix](https://cachix.org/) integration will magically beam any build steps already executed by the CI right onto your machine when calling Nix commands in the shell opened above.
On top of the local and remote Nix cache, we do still rely on CCache as well to make C/C++ build steps incremental, which are atomic steps from Nix's point of view.
If you add the `extra-sandbox-paths` line above, you **must** also set up that directory as follows:
```bash
sudo mkdir -m0770 -p /nix/var/cache/ccache
# macOS standard chown doesn't support --reference
nix shell .#nixpkgs.coreutils -c sudo chown --reference=/nix/store /nix/var/cache/ccache
```

# Basic Build Commands

From the Lean root directory inside the Lean shell:
```bash
nix build .#stage1  # build this stage's stdlib & executable
nix build .#stage1.test  # run all tests
nix run .#stage1.update-stage0  # update ./stage0 from this stage
nix run .#stage1.update-stage0-commit  # ...and commit the results
```
The `stage1.` part in each command is optional:
```bash
nix build .#test  # run tests for stage 1
nix build .  # build stage 1
nix build  # dito
```
On a build error, Nix will show the last 10 lines of the output by default. You can pass `-L` to `nix build` to show all lines, or pass the shown `*.drv` path to `nix log` to show the full log after the fact.

Keeping all outputs ever built on a machine alive can accumulate to quite impressive amounts of disk space, so you might want to trigger the Nix GC when /nix/store/ has grown too large:
```bash
nix-collect-garbage
```
This will remove everything not reachable from "GC roots" such as the `./result` symlink created by `nix build`, so you might want to call that first to keep your current stage 1 alive.

# Build Process Description

The Nix build process conceptually works the same as described in [Lean Build Pipeline](index.md#lean-build-pipeline).
However, there are two important differences in practice apart from the standard Nix properties (hermeneutic, reproducible builds stored in a global hash-indexed store etc.):
* Only files tracked by git (using `git add` or at least `git add --intent-to-add`) are compiled.
This is actually a general property of Nix flakes, and has the benefit of making it basically impossible to forget to commit a file (at least in `src/`).
* Only files reachable from `src/Lean.lean` are compiled.
This is because modules are discovered not from a directory listing anymore but by recursively compiling all dependencies of that top module.

# Emacs Integration

Starting a known-good (pinned) version of Emacs from the Lean shell with `lean4-mode` fully set up for development on Lean is as easy as:
```bash
nix run .#emacs-dev
```
Arguments can be passed as well:
```bash
nix run .#emacs-dev src/Lean.lean
```

Note that the UX of `emacs-dev` is quite different from the Make-based setup regarding the compilation of dependencies:
there is no mutable directory incrementally filled by the build that we could point the editor at for .olean files.
Instead, `emacs-dev` will gather the individual dependency outputs from the Nix store when checking a file -- and build them on the fly when necessary.
However, it will only ever load changes saved to disk, not ones opened in other buffers.

Because of technical limitations, there are currently two further restrictions for files in `src/`:
* They must be reachable from `src/Lean.lean` to be editable. Note that they have to be so anyway to be included in the full stage compilation, but it might initially be confusing when creating a new file.
* New imports, even when already compiled, will only be accessible after saving the file.

# Other Fun Stuff to Do with Nix

Open Emacs with Lean set up from an arbitrary commit (without even cloning Lean beforehand... if your Nix is new enough):
```bash
nix run github:leanprover/lean4/7e4edeb#emacs-package
```

Open a shell with `lean` and `LEAN_PATH` set up for compiling a specific module (this is exactly what `emacs-dev` is doing internally):
```bash
nix develop .#mods."Lean.Parser.Basic"
```

Not sure what you just broke? Run Lean from (e.g.) the previous commit on a file:
```bash
nix run .\?rev=$(git rev-parse @^) scratch.lean
```

...more surely to come...
