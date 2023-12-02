# Development Workflow

If you want to make changes to Lean itself, start by [building Lean](../make/index.md) from a clean checkout to make sure that everything is set up correctly.
After that, read on below to find out how to set up your editor for changing the Lean source code, followed by further sections of the development manual where applicable such as on the [test suite](testing.md) and [commit convention](commit_convention.md).

If you are planning to make any changes that may affect the compilation of Lean itself, e.g. changes to the parser, elaborator, or compiler, you should first read about the [bootstrapping pipeline](bootstrap.md).
You should not edit the `stage0` directory except using the commands described in that section when necessary.

## Development Setup

You can use any of the [supported editors](../setup.md) for editing the Lean source code.
If you set up `elan` as below, opening `src/` as a *workspace folder* should ensure that stage 0 (i.e. the stage that first compiles `src/`) will be used for files in that directory.

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

### `ccache`

Lean's build process uses [`ccache`](https://ccache.dev/) if it is
installed to speed up recompilation of the generated C code. Without
`ccache`, you'll likely spend more time than necessary waiting on
rebuilds - it's a good idea to make sure it's installed.
