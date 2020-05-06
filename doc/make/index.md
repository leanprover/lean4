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

Add `-jN` for an appropriate `N` to `make` for a parallel build.

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

Since version 4, Lean is a partially bootstrapped program: parts of the frontend
and compiler are written in Lean itself and thus need to be built before
building Lean itself - which is needed to again build those parts. This cycle is
broken by using pre-built C files checked into the repository (which ultimately
go back to a point where the Lean compiler was not written in Lean) in place of
these Lean inputs and then compiling everything in multiple stages up to a fixed
point:

* stage0: Compiled from C/C++ files in `stage0/src` of a previous version of Lean.
  This stage should always build since `stage0/` is not changed in the regular
  workflow.
* stage1: Compiled from Lean/C++ files in `src` using the stage0 compiler. This
  stage is usually sufficient for testing local changes.
* stage2: Compiled from Lean/C++ files in `src` using the stage1 compiler. This
  stage can be used to test changes in stage1 on the stdlib.
* stage3: Compiled from Lean/C++ files in `src` using the stage2 compiler. This
  stage is a sanity check and should usually be identical to stage2. The target
  `check-stage3` implements this check.

Each of these stages has a corresponding subdirectory in the CMake build folder.
They can be built by calling `make stageX` in the root build folder, or navigating
into the stage build folder and using more specific targets (e.g. `make test`).
`make` by itself in the root build folder is short for `make stage1`. Note that since
each stage is a separate CMake project, calling `make` inside a stage build folder
will never rebuild other stages.

Development Setup
-----------------

`make test`/`ctest` inside a stage build directory will automatically use the
corresponding Lean executables, but for running tests or compiling Lean programs
manually, you need to put them into your `PATH` yourself. A simple option for doing
that is to register them as custom toolchains in [`elan`](https://github.com/Kha/elan):
```
# in the Lean rootdir
elan toolchain link lean4 build/release/stage1
# make `lean` etc. point to the given build in the rootdir and subdirs
elan override set lean4
```
You can also use the `+toolchain` shorthand (e.g. `lean +lean4-debug`) to switch
toolchains on the spot.

Likewise for editor support, `elan` makes it simple to use a stage0 for editing 
the stdlib while using a different stage for all other files:
```
elan toolchain link lean4-stage0 build/release/stage0
cd src
elan override set lean4-stage0
```
Assuming `lean4-rootdir` is unset, `lean4-mode` will automatically use the
correct `lean` executable for the current file.

Troubleshooting
---------------

* Call `make` with an additional `VERBOSE=1` argument to print executed commands.

Further Information
-------------------

- [Measuring Code Coverage](coverage.md)
- [Compiling Lean with Split Stacks](split-stack.md)
