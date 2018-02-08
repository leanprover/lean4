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

Further Information
-------------------

- [Using CCache](ccache.md) to avoid recompilation
- [Measuring Code Coverage](coverage.md)
- [Compiling Lean with Split Stacks](split-stack.md)
