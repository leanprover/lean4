# Development Workflow

If you want to make changes to Lean itself, start by [building Lean](../make/index.md) from a clean checkout to make sure that everything is set up correctly.
After that, read on below to find out how to set up your editor for changing the Lean source code, followed by further sections of the development manual where applicable such as on the [test suite](testing.md) and [commit convention](commit_convention.md).

If you are planning to make any changes that may affect the compilation of Lean itself, e.g. changes to the parser, elaborator, or compiler, you should first read about the [bootstrapping pipeline](bootstrap.md).
You should not edit the `stage0` directory except using the commands described in that section when necessary.

## Development Setup

You can use any of the [supported editors](https://lean-lang.org/install/manual/) for editing the Lean source code.
Please see below for specific instructions for VS Code.

### Dev setup using elan

You can use [`elan`](https://github.com/leanprover/elan) to easily
switch between stages and build configurations based on the current
directory, both for the `lean`, `leanc`, and `leanmake` binaries in your shell's
PATH and inside your editor.

To install elan, you can do so, without installing a default version of Lean, using (Unix)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none
```
or (Windows)
```
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -f elan-init.ps1 --default-toolchain none
del elan-init.ps1
```

The `lean-toolchain` files in the Lean 4 repository are set up to use the `lean4-stage0`
toolchain for editing files in `src` and the `lean4` toolchain for editing files in `tests`.

Run the following commands to make `lean4` point at `stage1` and `lean4-stage0` point at `stage0`:
```bash
# in the Lean rootdir
elan toolchain link lean4 build/release/stage1
elan toolchain link lean4-stage0 build/release/stage0
```

You can also use the `+toolchain` shorthand (e.g. `lean +lean4-debug`) to switch
toolchains on the spot. `lean4-mode` will automatically use the `lean` executable
associated with the directory of the current file as long as `lean4-rootdir` is
unset and `~/.elan/bin` is in your `exec-path`. Where Emacs sources the
`exec-path` from can be a bit unclear depending on your configuration, so
alternatively you can also set `lean4-rootdir` to `"~/.elan"` explicitly.

You might find that debugging through elan, e.g. via `gdb lean`, disables some
things like symbol autocompletion because at first only the elan proxy binary
is loaded. You can instead pass the explicit path to `bin/lean` in your build
folder to gdb, or use `gdb $(elan which lean)`.

It is also possible to generate releases that others can use,
simply by pushing a tag to your fork of the Lean 4 github repository
(and waiting about an hour; check the `Actions` tab for completion).
If you push `my-tag` to a fork in your github account `my_name`,
you can then put `my_name/lean4:my-tag` in your `lean-toolchain` file in a project using `lake`.
(You must use a tag name that does not start with a numeral, or contain `_`).

### VS Code

There is a `lean.code-workspace` file that correctly sets up VS Code with workspace roots for the stage0/stage1 setup described above as well as with other settings.
You should always load it when working on Lean, such as by invoking
```
code lean.code-workspace
```
on the command line.

You can use the `Refresh File Dependencies` command as in other projects to rebuild modules from inside VS Code but be aware that this does not trigger any non-Lake build targets.
In particular, after updating `stage0/` (or fetching an update to it), you will want to invoke `make` directly to rebuild `stage0/bin/lean` as described in [building Lean](../make/index.md).
You should then run the `Restart Server` command to update all open files and the server watchdog process as well.

### `ccache`

Lean's build process uses [`ccache`](https://ccache.dev/) if it is
installed to speed up recompilation of the generated C code. Without
`ccache`, you'll likely spend more time than necessary waiting on
rebuilds - it's a good idea to make sure it's installed.

### `prelude`
Unlike most Lean projects, all submodules of the `Lean` module begin with the
`prelude` keyword. This disables the automated import of `Init`, meaning that
developers need to figure out their own subset of `Init` to import. This is done
such that changing files in `Init` doesn't force a full rebuild of `Lean`.

### Testing against Mathlib/Batteries
You can test a Lean PR against Mathlib and Batteries by rebasing your PR
on to `nightly-with-mathlib` branch. (It is fine to force push after rebasing.)
CI will generate a branch of Mathlib and Batteries called `lean-pr-testing-NNNN`
on the `leanprover-community/mathlib4-nightly-testing` fork of Mathlib.
This branch uses the toolchain for your PR, and will report back to the Lean PR with results from Mathlib CI.
See https://leanprover-community.github.io/contribute/tags_and_branches.html for more details.

### Testing against the Lean Language Reference
You can test a Lean PR against the reference manual by rebasing your PR
on to `nightly-with-manual` branch. (It is fine to force push after rebasing.)
CI will generate a branch of the reference manual called `lean-pr-testing-NNNN`
in `leanprover/reference-manual`. This branch uses the toolchain for your PR,
and will report back to the Lean PR with results from Mathlib CI.

### Avoiding rebuilds for downstream projects

If you want to test changes to Lean on downstream projects and would like to avoid rebuilding modules you have already built/fetched using the project's configured Lean toolchain, you can often do so as long as your build of Lean is close enough to that Lean toolchain (compatible .olean format including structure of all relevant environment extensions).

To override the toolchain without rebuilding for a single command, for example `lake build` or `lake lean`, you can use the prefix
```
LEAN_GITHASH=$(lean --githash) lake +lean4 ...
```
Alternatively, use
```
export LEAN_GITHASH=$(lean --githash)
export ELAN_TOOLCHAIN=lean4
```
to persist these changes for the lifetime of the current shell, which will affect any processes spawned from it such as VS Code started via `code .`.
If you use a setup where you cannot directly start your editor from the command line, such as VS Code Remote, you might want to consider using [direnv](https://direnv.net/) together with an editor extension for it instead so that you can put the lines above into `.envrc`.
