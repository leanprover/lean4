Requirements
------------

- C++14 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)

Platform-Specific Setup
-----------------------

- [Linux (Ubuntu)](ubuntu.md)
- [Windows (msys2)](msys2.md)
- [Windows (Visual Studio)](msvc.md)
- [macOS (homebrew)](osx-10.9.md)
- Linux/macOS/WSL via [Nix](https://nixos.org/nix/): Call `nix-shell` in the project root. That's it.

Generic Build Instructions
--------------------------

Setting up a basic release build:

```bash
git clone https://github.com/leanprover/lean4
cd lean
mkdir -p build/release
cd build/release
cmake ../..
make
```

Setting up a basic debug build:

```bash
git clone https://github.com/leanprover/lean4
cd lean
mkdir -p build/debug
cd build/debug
cmake -D CMAKE_BUILD_TYPE=DEBUG ../..
make
```

This will compile the Lean library and binary into the `stage0.5` subfolder; see
below for details. Add `-jN` for an appropriate `N` to `make` for a parallel
build.

Useful CMake Configuration Settings
-----------------------------------

Pass these along with the `cmake ../..` command.

* `-D CMAKE_BUILD_TYPE=`\
  Select the build type. Valid values are `RELEASE` (default), `DEBUG`,
  `RELWITHDEBINFO`, and `MINSIZEREL`.

* `-D CMAKE_C_COMPILER=`\
  `-D CMAKE_CXX_COMPILER=`\
  Select the C/C++ compilers to use. Official Lean releases currently use Clang;
  see also `.github/workflows/ci.yml` for the CI config.

* `-D CHECK_OLEAN_VERSION=OFF`\
  The `.olean` files are tagged with the Lean version they were produced with.
  This means that by default, the core library has to be recompiled after e.g.
  every `git commit`. Use this option to avoid the version check. The `.olean`
  files can be removed manually by invoking `make clean-olean`.

Lean will automatically use [CCache](https://ccache.dev/) if available to avoid
redundant builds, especially after stage 0 has been updated (see below).

Lean Build Pipeline
-------------------

Since version 4, Lean is a partially bootstrapped program: most parts of the
frontend and compiler are written in Lean itself and thus need to be built before
building Lean itself - which is needed to again build those parts. This cycle is
broken by using pre-built C files checked into the repository (which ultimately
go back to a point where the Lean compiler was not written in Lean) in place of
these Lean inputs and then compiling everything in multiple stages up to a fixed
point. The build directory is organized in these stages:

```bash
stage0/
  bin/
    lean  # the Lean compiler & server
    leanc  # a wrapper around a C compiler supplying search paths etc
    leanmake  # a wrapper around `make` supplying the Makefile below
  lib/
    lean/**/*.olean  # the Lean library (incl. the compiler) compiled by `lean` above
    temp/**/*.{c,o}  # the library extracted to C and compiled by `leanc`
    libInit.a  # a static library of the Lean library
    libleancpp.a  # a static library of the C++ sources of Lean
  include/
    config.h  # config variables used to build `lean` such as use allocator
    runtime/lean.h  # runtime headers, used by extracted C code, uses `config.h`
  share/lean/
    Makefile  # used by `leanmake`
stage1/...
stage2/...
stage3/...
```

The build for each stage starts by assembling `bin/lean` from the `libInit.a` of
the preceding stage and `libleancpp.a` built from `src/`; in the case of stage 0,
which doesn't have a preceding stage, both libraries are instead assembled from
`stage0/src`, which contains the C++ and extracted C code of a previous commit of
Lean. This Lean binary is then used to compile the Lean library into .olean files
and ultimately a new `libInit.a`, which is then used by the next stage.

Each stage can be built by calling `make stageN` in the root build folder. It is
usually not necessary to compile all stages in order to test a change. Stage 3 in
fact should usually be identical to stage 2 and only exists as a sanity check,
which can be done via `make check-stage3`. Building stage 2 should only be
necessary for testing how changes in the compiler influence compilation of the
compiler itself, e.g. checking if an optimization speeds up (or breaks) the
compiler. Stage 1 is sufficient for testing changes on the library and test
programs. In fact, if the stage 0 library and the stage 1 are compatible (use the
same Lean ABI, so to speak), we can avoid even rebuilding the stage 1 library
using a special stage "0.5" that combines the stage 1 compiler with the stage 0
library. Most changes do not break this ABI, so running `make` by itself in the
root build folder will default to `make stage0.5`. In summary, doing a standard
build via `make` involves these steps:

1. compile the `stage0/src` archived sources into `stage0/bin/lean`
1. use it to compile the library (*including* your changes) into `stage0/lib`
1. link that and the *current* C++ code from `src/` into `stage1/bin/lean`
1. copy ("uplift") the Lean library from `stage0/lib` into `stage1/lib`

You now have a Lean binary and library that include your changes, though their
own compilation was not influenced by them, that you can use to test your changes
on test programs whose compilation *will* be influenced by the changes.

Finally, when we want to use new language features in the library, we need to
update the stage 0 compiler, which can be done via `make -C stageN update-stage0`.
Note: you cannot do this for stage 0.5 because the extracted C files are not
copied over from stage 0 to that stage, so just use stage 0 instead.
`make update-stage0` without `-C` defaults to stage0 for this reason. If updating
stage 0 from stage 0 sounds wrong to you, just remember that the stage 0 build
directory contains the *output* of the stage 0 compiler!

Development Setup
-----------------

After building a stage, you can invoke `make -C stageN test` (or, even better,
`make -C stageN ARGS=-j` to make `ctest` parallel) to run the Lean test suite.
`make test` without `-C` defaults to stage 0.5. While the Lean tests
will automatically use that stage's corresponding Lean executables, for running
tests or compiling Lean programs manually, you need to put them into your `PATH`
yourself. A simple option for doing that is to use
[`elan`](https://github.com/Kha/elan), see the next section.

The only currently supported editor is Emacs, see `lean4-mode/README.md` for
basic setup. You can set `lean4-rootdir` manually to tell it what stage to use:
```
# while editing the Lean library
M-x set-variable lean4-rootdir RET ".../build/release/stage0" RET
# while testing, using a Lean that includes your changes
M-x set-variable lean4-rootdir RET ".../build/release/stage0.5" RET
```
but `elan` again makes it simple to do that automatically, see below.

Dev setup using elan
--------------------

You can use [`elan`](https://github.com/Kha/elan) to easily switch between
stages and build configurations based on the current directory, both for the
`lean/leanc/leanmake` binaries in your shell's PATH and inside Emacs.

If you haven't already installed elan, you can do so, without installing a
default version of Lean, using
```bash
curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none
```
You can use `elan toolchain link` to give a specific stage build directory a
reference name, then use `elan override set` to associate such a name to the
current directory. We usually want to use `stage0` for editing files in `src`
and `stage0.5` for everything else (e.g. tests).
```
# in the Lean rootdir
elan toolchain link lean4 build/release/stage0.5
elan toolchain link lean4-stage0 build/release/stage0
# make `lean` etc. point to stage0.5 in the rootdir and subdirs
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

Troubleshooting
---------------

* Call `make` with an additional `VERBOSE=1` argument to print executed commands.
