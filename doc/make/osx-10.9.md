# Install Packages on OS X

We assume that you are using [homebrew][homebrew] as a package manager.

[homebrew]: http://brew.sh

## Compilers

You need a C++14-compatible compiler to build Lean. As of July
2025, you have three options:

 - clang++ shipped with OSX (at time of writing v17.0.0)
 - clang++ via homebrew (at time of writing, v20.1.8)
 - gcc via homebrew (at time of writing, v15.1.0)

We recommend to use Apple's clang++ because it is pre-shipped with OS
X and requires no further installation.

To install gcc via homebrew, please execute:
```bash
brew install gcc
```
To install clang via homebrew, please execute:
```bash
brew install llvm lld
```
To use compilers other than the default one (Apple's clang++), you
need to use `-DCMAKE_CXX_COMPILER` option to specify the compiler
that you want to use when you run `cmake`. For example, do the
following to use `g++`.
```bash
cmake -DCMAKE_CXX_COMPILER=g++ ...
```

## Required Packages: CMake, GMP, libuv, pkgconf

```bash
brew install cmake
brew install gmp
brew install libuv
brew install pkgconf
```

## Recommended Packages: CCache

```bash
brew install ccache
```
