# Development Workflow
- [Commit Convention](./commit_convention.md)
- [Building Lean](../make/index.md)
  - [Ubuntu Setup](../make/ubuntu-16.04.md)
  - [macOS Setup](../make/osx-10.9.md)
  - [Windows MSYS2 Setup](../make/msys2.md)
  - [Windows with WSL](../make/wsl.md)
  - [Nix Setup (*Experimental*)](../make/nix.md)
- [Unit Testing](./testing.md)
- [Building This Manual](./mdbook.md)
- [Fixing Tests](./fixing_tests.md)
- [Debugging](./debugging.md)
- [C++ Coding Style](./dev/cpp_coding_style.md)

You will notice there is a `stage0` folder. This is for bootstrapping
the compiler development.  Generally you do not change any code in
`stage0` manually.  It is important that you read [bootstrapping
pipeline](bootstrap.md) so you understand how this works.

The dev team uses `elan` to manage which `lean` toolchain to use
locally and `elan` can be used to setup the version of Lean you are
manually building.  This means you generally do not use `make
install`. You use `elan` instead.

## Development Setup

You can use any of the [supported editors](../setup.md) for editing
the Lean source code. If you set up `elan` as below, opening `src/` as
a *workspace folder* should ensure that stage 0 will be used for file
in that directory. You should also set the `LEAN_SRC_PATH` environment
variable to the path of the `src/` directory to enable
go-to-definition in the stdlib (automatically set when using
`nix-shell`).

## Dev setup using elan

You can use [`elan`](https://github.com/leanprover/elan) to easily
switch between stages and build configurations based on the current
directory, both for the `lean/leanc/leanmake` binaries in your shell's
PATH and inside your editor.

To install elan, you can do so, without installing a default version of Lean, using
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none
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
