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
- [Windows (WSL)](wsl.md)
- [macOS (homebrew)](osx-10.9.md)
- Linux/macOS/WSL via [Nix](https://nixos.org/nix/): Call `nix-shell` in the project root. That's it.
- There is also an [**experimental** setup based purely on Nix](nix.md) that works fundamentally differently from the
  make/CMake setup described on this page.

Generic Build Instructions
--------------------------

Setting up a basic release build:

```bash
git clone https://github.com/leanprover/lean4
cd lean4
mkdir -p build/release
cd build/release
cmake ../..
make
```

Note: that if you have a CPU with lots of cores you will get a faster
build if you specify the number of parallel jobs using the `-j n`
option on make.

For example, on an AMD Ryzen 9 `make` takes 00:04:55, whereas `make -j 10`
takes 00:01:38.  Your results may vary depending on the speed of your hard
drive.

Setting up a basic debug build:

```bash
git clone https://github.com/leanprover/lean4
cd lean4
mkdir -p build/debug
cd build/debug
cmake -D CMAKE_BUILD_TYPE=DEBUG ../..
make
```

This will compile the Lean library and binary into the `stage1` subfolder; see
below for details. Add `-jN` for an appropriate `N` to `make` for a parallel
build.

To install the build see [Dev setup using
elan](../dev/index.md#dev-setup-using-elan).


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

Lean will automatically use [CCache](https://ccache.dev/) if available to avoid
redundant builds, especially after stage 0 has been updated.

Troubleshooting
---------------

* Call `make` with an additional `VERBOSE=1` argument to print executed commands.
