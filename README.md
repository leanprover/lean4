<table>
  <tr>
    <th>Ubuntu</th><th>OS X</th><th>Windows</th><th>Coverage</th><th>Builds / UnitTests / Dynamic Analyses</th>
  </tr>
  <tr>
    <td><a href="https://travis-ci.org/leodemoura/lean"><img src="https://travis-ci.org/leodemoura/lean.png?branch=master" title="Ubuntu 12.04 LTS 64bit, g++-4.8 | clang++-3.3"/></a></td>
    <td><a href="https://travis-ci.org/soonhokong/lean-osx"><img src="https://travis-ci.org/soonhokong/lean-osx.png?branch=master" title="Mac OS X 10.8.2, g++-4.9"/></a></td>
    <td><a href="https://travis-ci.org/soonhokong/lean-windows"><img src="https://travis-ci.org/soonhokong/lean-windows.png?branch=master" title="Windows, x86_64-w64-mingw32-g++-4.8.2"/></a></td>
    <td><a href="https://coveralls.io/r/soonhokong/lean?branch=master"><img src="https://coveralls.io/repos/soonhokong/lean/badge.png?branch=master"/></a></td>
    <td><a href="http://build.leanprover.net">http://build.leanprover.net</a></td>
  </tr>
</table>

**Remark: Lean 0.2 is under development. To try Lean, please use [version 0.1](https://github.com/leodemoura/lean0.1).**

About
-----

- [Design](doc/design.md)
- [To Do list](doc/todo.md)
- [Authors](doc/authors.md)
- [Tutorial](doc/lean/tutorial.md)

Requirements
------------

- C++11 compatible compiler: [g++](http://gcc.gnu.org/) (version >= 4.8.1), or [clang++](http://clang.llvm.org/cxx_status.html) (version >= 3.3)
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)
- [MPFR (GNU MPFR Library)](http://www.mpfr.org/)
- [Lua 5.2 or 5.1](http://www.lua.org), or [LuaJIT 2.0](http://luajit.org)
- (optional) [gperftools](https://code.google.com/p/gperftools/)
- (optional) [Boost](http://www.boost.org) (version >= 1.54), we can
  build Lean using boost::thread instead of std::thread. When using
  Boost, Lean can modify the thread stack size.

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
