[![Build Status](https://travis-ci.org/leodemoura/lean.png?branch=master)](https://travis-ci.org/leodemoura/lean)
Ubuntu 12.04 LTS 64bit, g++-4.8 | clang++-3.3

[![Build Status](https://travis-ci.org/soonhokong/lean-osx.png?branch=master)](https://travis-ci.org/soonhokong/lean-osx)
Mac OS X 10.8.2, g++-4.9

[![Build Status](https://travis-ci.org/soonhokong/lean-windows.png?branch=master)](https://travis-ci.org/soonhokong/lean-windows)
Windows, x86_64-w64-mingw32-g++-4.8.1

[[Result of Build/UnitTest/Coverage/Dynamic Analysis]][build]

[build]: http://build.leanprover.net

About
-----

- [Design](doc/design.md)
- [To Do list](doc/todo.md)
- [Authors](doc/authors.md)

Requirements
------------

- C++11 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)
- [MPFR (GNU MPFR Library)](http://www.mpfr.org/)
- (optional) [gperftools](https://code.google.com/p/gperftools/)

Installing required packages at
--------------------------------

- [Ubuntu 12.04](doc/make/ubuntu-12.04.md)
- [Ubuntu 12.04 (detailed)](doc/make/ubuntu-12.04-detailed.md)
- [Fedora 19](doc/make/fedora-19.md)
- [OS X 10.8](doc/make/osx-10.8.md)
- [Cygwin](doc/make/cygwin.md)

Build Instructions
------------------

- [CMake + Make](doc/make/cmake_make.md)
- [CMake + Ninja](doc/make/cmake_ninja.md)
- [Faster builds with ccache](doc/make/ccache.md)

Miscellaneous
-------------

- [Testing and Code Coverage](doc/make/coverage.md)
- Building Doxygen Documentation: `doxygen src/Doxyfile`
- [Coding style](doc/style.md)
