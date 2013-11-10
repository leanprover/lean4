[![Build Status](https://travis-ci.org/leodemoura/lean.png?branch=master)](https://travis-ci.org/leodemoura/lean)
Ubuntu 12.04 LTS 64bit, g++-4.8 | clang++-3.3

[![Build Status](https://travis-ci.org/soonhokong/lean-osx.png?branch=master)](https://travis-ci.org/soonhokong/lean-osx)
Mac OS X 10.8.2, g++-4.9

[![Build Status](https://travis-ci.org/soonhokong/lean-windows.png?branch=master)](https://travis-ci.org/soonhokong/lean-windows)
Windows, x86_64-w64-mingw32-g++-4.8.2

[![Coverage Status](https://coveralls.io/repos/soonhokong/lean/badge.png?branch=master)](https://coveralls.io/r/soonhokong/lean?branch=master)

[[Result of Build/UnitTest/Coverage/Dynamic Analysis]][build]

[build]: http://build.leanprover.net

About
-----

- [Design](doc/design.md)
- [To Do list](doc/todo.md)
- [Authors](doc/authors.md)

Requirements
------------

- C++11 compatible compiler: [g++](http://gcc.gnu.org/) (version >= 4.8.1), or [clang++](http://clang.llvm.org/cxx_status.html) (version >= 3.3)
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)
- [MPFR (GNU MPFR Library)](http://www.mpfr.org/)
- [Lua 5.2 or 5.1](http://www.lua.org), or [LuaJIT 2.0](http://luajit.org)
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
- [Coding style](doc/coding_style.md)
- [Git Commit Convention](doc/commit_convention.md)
- [Automatic builds](doc/make/travis.md)
