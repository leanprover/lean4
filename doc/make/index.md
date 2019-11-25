Requirements
------------

- C++14 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)

Platform-Specific Setup
-----------------------

- [Linux (Ubuntu)](ubuntu-16.04.md)
- [Windows (msys2)](msys2.md)
- [Windows (Visual Studio)](msvc.md)
- [macOS (homebrew)](osx-10.9.md)
- Linux/macOS ([Nix](https://nixos.org/nix/)): call `nix-shell` in the project root
- [Emscripten: lean.js](emscripten.md)

Generic Build Instructions
--------------------------

Setting up a basic release build using `make`:

```bash
git clone https://github.com/leanprover/lean
cd lean
mkdir -p build/release
cd build/release
cmake ../../src
make
```

Setting up a basic debug build using `make`:

```bash
git clone https://github.com/leanprover/lean
cd lean
mkdir -p build/debug
cd build/debug
cmake -D CMAKE_BUILD_TYPE=DEBUG ../../src
make
```

Useful CMake Configuration Settings
-----------------------------------

Pass these along with the `cmake ../../src` command.

* `-G Ninja`\
  CMake 2.8.11 supports the [Ninja](https://ninja-build.org/) build system.
  [Some people report][ninja_work] that using
  Ninja can reduce the build time, esp when a build is
  incremental. Call `ninja` instead of `make` to build the project.

  [ninja_work]: https://plus.google.com/108996039294665965197/posts/SfhrFAhRyyd

* `-D CMAKE_BUILD_TYPE=`\
  Select the build type. Valid values are `RELEASE` (default), `DEBUG`,
  `RELWITHDEBINFO`, and `MINSIZEREL`.

* `-D CMAKE_C_COMPILER=`\
  `-D CMAKE_CXX_COMPILER=`\
  Select the C++ compiler to use.

* `-D CHECK_OLEAN_VERSION=OFF`\
  The `.olean` files are tagged with the Lean version they were produced with.
  This means that by default, the core library has to be recompiled after e.g.
  every `git commit`. Use this option to avoid the version check. The `.olean`
  files can be removed manually by invoking `make/ninja clean-olean`.

Lean will automatically use [CCache](https://ccache.dev/) if available to avoid
redundant builds, especially after stage 0 has been updated (see below).

Lean Build Pipeline
-------------------

Since version 4, Lean is a partially bootstrapped program: parts of the frontend
and compiler are written in Lean itself and thus need to be built before
building Lean itself - which is needed to again build those parts. Building the
`lean` executable (e.g. via `make bin`) involves roughly the following steps:

* The target `stage0` compiles an initial `lean` executable directly from C/C++
  code versioned in `stage0/` (via a CMake `ExternProject`). The C++ code is a
  previous version of the code in `src/`, while the C code was extracted from
  the Lean stdlib of the same commit.
* Using this executable, the stdlib contained in `library/` is compiled to
  `.olean` object files as well as extracted to C in `src/stage1` by the target
  `make_stdlib`.
* The static libraries `leanstdlib` and `leanstatic` are built from the extracted
  files and the current C++ code in `src/`, respectively.
* These libraries are linked into the final `lean` executable.
* The `bin` target finally copies all these objects into `bin/`. The initial
  `lean` executable is called `lean_stage0` there.

Development Workflows
---------------------

* The `make_stdlib` target can be used to check the standard library without
  rebuilding `lean`.
* In most cases, the `bin` target can be used to build and test either a Lean or
  C++ change. The `lean` target can be used to build the same binary without copying
  it to `bin/`, which can be useful for quickly building a debug version without
  changing the binary used by the editor. The `LEAN_PATH` variable may need to be set
  to the location of `library/` manually in this case.
* Changes in the frontend or compiler do not immediately affect the stdlib because of
  the staged build until stage0 is updated by making the `update-stage0` target, after
  which the stdlib can be updated appropriately if necessary.

Troubleshooting
---------------

* The `Makefile` at `library/` does not need to be invoked directly. However,
  we may want to do it while investigating problems, e.g., Lean is looping while
  compiling a file. To manually invoke this `Makefile`, we should use:
```bash
cd library/
STAGE1_OUT=<build_dir_path>/stage1 make <build_dir_path>/stage1/libleanstdlib.a
```
For example, if our build directory is located at `build/release/`, the command above should be
```bash
cd library/
STAGE1_OUT=../build/release/stage1 make ../build/release/stage1/libleanstdlib.a
```

Further Information
-------------------

- [Using CCache](ccache.md) to avoid recompilation
- [Measuring Code Coverage](coverage.md)
- [Compiling Lean with Split Stacks](split-stack.md)
