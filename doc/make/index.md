Requirements
------------

- C++11 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)

Platform-Specific Setup
-----------------------

- [Linux (Ubuntu)](ubuntu-16.04.md)
- [Windows (msys2)](msys2.md)
- [Windows (Visual Studio)](msvc.md)
- [macOS](osx-10.9.md)
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

* `-G Ninja`
  CMake 2.8.11 supports the [Ninja](https://ninja-build.org/) build system.
  [Some people report][ninja_work] that using
  Ninja can reduce the build time, esp when a build is
  incremental. Call `ninja` instead of `make` to build the project.
  
  [ninja_work]: https://plus.google.com/108996039294665965197/posts/SfhrFAhRyyd
  
* `-D CMAKE_BUILD_TYPE=`
  Select the build type. Valid values are `RELEASE` (default), `DEBUG`,
  `RELWITHDEBINFO`, and `MINSIZEREL`.

* `-D CMAKE_CXX_COMPILER=`
  Select the C++ compiler to use.

* `-D LEAN_IGNORE_OLEAN_VERSION`
  The `.olean` files are tagged with the Lean version they were produced with.
  This means that by default, the core library has to be recompiled after e.g.
  every `git commit`. Use this option to avoid the version check. The `.olean`
  files can be removed manually by invoking `make/ninja clean-olean`.

Lean Build Pipeline
-------------------

Since version 4, Lean is a partially bootstrapped program: parts of the frontend
and compiler are written in Lean itself and thus need to be built before
building Lean itself - which is needed to again build those parts. Building the
`lean` executable (e.g. via `make bin`) involves roughly the following steps:

* An initial executable `lean_stage0` is compiled directly from the repository
  contents (binaries are generally built by a target of the same name). These
  include:
  * `src/stage0`: the Lean standard library extracted to C++ from a previous
    commit
  * other parts of `src/`: the non-bootstrapped parts of Lean written in C++
* Using `lean_stage0`, the stdlib contained in `library/` is compiled to
  `.olean` object files as well as extracted to C++ in `src/stage1` by the
  target `stdlib`.
* The target `build_libleanstdlib` builds the static library
  `stage1/libleanstdlib.a` from the extracted files.
* This library is linked with the C++ source files into `libleanstatic.a` and
  ultimately into the executable `lean`.
* The `bin` target finally copies the executable and libraries into `bin/`.

Development Workflows
---------------------

* The `stdlib` target can be used to check the standard library without
  rebuilding `lean`.
* In most cases, the `bin` target can be used to build and test either a Lean or
  C++ change. The `lean` target can be used to build the same binary without copying
  it to `bin/`, which can be useful for quickly building a debug version without
  changing the binary used by the editor. The `LEAN_PATH` variable may need to be set
  to the location of `library/` manually in this case.
* When making a parallel change in both Lean and C++, there usually is no simple
  way of writing C++ code that builds in both stage0 and stage1. In this case,
  temporarily set `-DREBUILD_STAGE0=OFF` to deactivate rebuilding `lean_stage0`,
  which, as described above, is used to compile the standard library. When the
  change is complete and stage1 is working as expected, make the target
  `update-stage0` to copy stage1 to stage0 - this is the re-bootstrapping step.
  Reactivate `REBUILD_STAGE0` and stage0 should compile again.

Further Information
-------------------

- [Using CCache](ccache.md) to avoid recompilation
- [Measuring Code Coverage](coverage.md)
- [Compiling Lean with Split Stacks](split-stack.md)
