# Install Packages on OS X 14.5

We assume that you are using [homebrew][homebrew] as a package manager.

[homebrew]: http://brew.sh

## Compilers

You need a C++11-compatible compiler to build Lean. As of November
2014, you have three options:

 - clang++-3.5 (shipped with OSX, Apple LLVM version 6.0)
 - gcc-4.9.1 (homebrew)
 - clang++-3.5 (homebrew)

We recommend to use Apple's clang++ because it is pre-shipped with OS
X and requires no further installation.

To install gcc-4.9.1 via homebrew, please execute:
```bash
brew install gcc
```
To install clang++-3.5 via homebrew, please execute:
```bash
brew install llvm
```
To use compilers other than the default one (Apple's clang++), you
need to use `-DCMAKE_CXX_COMPILER` option to specify the compiler
that you want to use when you run `cmake`. For example, do the
following to use `g++`.
```bash
cmake -DCMAKE_CXX_COMPILER=g++ ...
```

## Required Packages: CMake, GMP, libuv

```bash
brew install cmake
brew install gmp
brew install libuv
```

## Recommended Packages: CCache

```bash
brew install ccache
```
