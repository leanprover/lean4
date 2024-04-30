Requirements
------------

- C++14 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)

Platform-Specific Setup
-----------------------

- [Linux (Ubuntu)](ubuntu.md)
- [Windows (msys2)](msys2.md)
- [Windows (WSL)](wsl.md)
- [macOS (homebrew)](osx-10.9.md)
- Linux/macOS/WSL via [Nix](https://nixos.org/nix/): Call `nix develop` in the project root. That's it.

Generic Build Instructions
--------------------------

Setting up a basic parallelized release build:

```bash
git clone https://github.com/leanprover/lean4
cd lean4
cmake --preset release
cmake --build --preset release -j$(nproc)
```
On macOS, replace `$(nproc)` with the desired parallelism amount.

The above commands will compile the Lean library and binaries into the
`stage1` subfolder; see below for details.

You should not usually run `cmake --install` after a successful build.
See [Dev setup using elan](../dev/index.md#dev-setup-using-elan) on how to properly set up your editor to use the correct stage depending on the source directory.

Useful CMake Configuration Settings
-----------------------------------

Pass these along with the `cmake --preset release` command.
There are also two alternative presets that combine some of these options you can use instead of `release`: `debug` and `sandebug` (sanitize + debug).

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

* Call `cmake --build` with an additional `-- VERBOSE=1` argument to print executed commands.
