# Building with Nix

While [Nix](https://nixos.org/nix/) can be used to quickly open a shell with all dependencies for the [standard setup](index.md) installed, the user-facing [Nix Setup](../setup.md#nix-setup) can also be used to work *on* Lean.

## Setup

Follow the setup in the link above; to open the Lean shell inside a Lean checkout, you can also use
```bash
# in the Lean root directory
$ nix-shell -A nix
```

On top of the local and remote Nix cache, it helps to we do still rely on CCache as well to make C/C++ build steps incremental, which are atomic steps from Nix's point of view.
To enable CCache, add the following line to the config file mentioned in the setup:
```bash
extra-sandbox-paths = /nix/var/cache/ccache
```
Then set up that directory as follows:
```bash
sudo mkdir -m0770 -p /nix/var/cache/ccache
# macOS standard chown doesn't support --reference
nix shell .#nixpkgs.coreutils -c sudo chown --reference=/nix/store /nix/var/cache/ccache
```

## Basic Build Commands

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

## Build Process Description

The Nix build process conceptually works the same as described in [Lean Build Pipeline](index.md#lean-build-pipeline).
However, there are two important differences in practice apart from the standard Nix properties (hermeneutic, reproducible builds stored in a global hash-indexed store etc.):
* Only files tracked by git (using `git add` or at least `git add --intent-to-add`) are compiled.
This is actually a general property of Nix flakes, and has the benefit of making it basically impossible to forget to commit a file (at least in `src/`).
* Only files reachable from `src/Lean.lean` are compiled.
This is because modules are discovered not from a directory listing anymore but by recursively compiling all dependencies of that top module.

## Editor Integration

As in the standard Nix setup.
After adding `src/` as an LSP workspace, it should automatically fall back to using stage 0 in there.

Note that the UX of `emacs/vscode-dev` is quite different from the Make-based setup regarding the compilation of dependencies:
there is no mutable directory incrementally filled by the build that we could point the editor at for .olean files.
Instead, `emacs-dev` will gather the individual dependency outputs from the Nix store when checking a file -- and build them on the fly when necessary.
However, it will only ever load changes saved to disk, not ones opened in other buffers.

## Other Fun Stuff to Do with Nix

Open Emacs with Lean set up from an arbitrary commit (without even cloning Lean beforehand... if your Nix is new enough):
```bash
nix run github:leanprover/lean4/7e4edeb#emacs-package
```

Open a shell with `lean` and `LEAN_PATH` set up for compiling a specific module (this is exactly what `emacs-dev` is doing internally):
```bash
nix develop .#mods.\"Lean.Parser.Basic\"
# alternatively, directly pass a command to execute:
nix develop .#stage2.mods.\"Init.Control.Basic\" -c bash -c 'lean $src -Dtrace.Elab.command=true'
```

Not sure what you just broke? Run Lean from (e.g.) the previous commit on a file:
```bash
nix run .\?rev=$(git rev-parse @^) scratch.lean
```

Work on two adjacent stages at the same time without the need for repeatedly updating and reverting `stage0/`:
```bash
# open an editor that will use only committed changes (so first commit them when changing files)
nix run .#HEAD-as-stage1.emacs-dev&
# open a second editor that will use those commited changes as stage 0
# (so don't commit changes done here until you are done and ran a final `update-stage0-commit`)
nix run .#HEAD-as-stage0.emacs-dev&
```
To run `nix build` on the second stage outside of the second editor, use
```bash
nix build .#stage0-from-input
```
This setup will inadvertently change your `flake.lock` file, which you can revert when you are done.

...more surely to come...

## Debugging

Since Nix copies all source files before compilation, you will need to map debug symbols back to the original path using `set substitute-path` in GDB.
For example, for a build on Linux with the Nix sandbox activated:
```bash
(gdb) f
#1  0x0000000000d23a4f in lean_inc (o=0x1) at /build/source/build/include/lean/lean.h:562
562	/build/source/build/include/lean/lean.h: No such file or directory.
(gdb) set substitute-path /build/source/build src
(gdb) f
#1  0x0000000000d23a4f in lean_inc (o=0x1) at /build/source/build/include/lean/lean.h:562
562	static inline void lean_inc(lean_object * o) { if (!lean_is_scalar(o)) lean_inc_ref(o); }
```
