# Development Workflow

If you want to make changes to Lean itself, start by [building Lean](../make/index.html) from a clean checkout to make sure that everything is set up correctly.
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

You can use `elan toolchain link` to give a specific stage build
directory a reference name, then use `elan override set` to associate
such a name to the current directory. We usually want to use `stage0`
for editing files in `src` and `stage1` for everything else (e.g.
tests).
```bash
# in the Lean rootdir
elan toolchain link lean4 build/release/stage1
elan toolchain link lean4-stage0 build/release/stage0
# make `lean` etc. point to stage1 in the rootdir and subdirs
elan override set lean4
cd src
# make `lean` etc. point to stage0 anywhere inside `src`
elan override set lean4-stage0
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
