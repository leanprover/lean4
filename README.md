<p align=center><a href="https://leanprover.github.io"><img src="https://leanprover.github.io/images/lean_logo.svg" alt="logo" width="300px"/></a></p>
<table>
  <tr>
    <th>License</th><th>Windows</th><th>Ubuntu</th><th>OS X</th><th>Coverage</th><th>Builds/Tests</th><th>Static Analysis</th>
  </tr>
  <tr>
    <td><a href="LICENSE"><img src="https://img.shields.io/badge/license-APACHE_2-green.svg?dummy" title="License"/></a></td>
    <td><a href="https://travis-ci.org/soonhokong/lean-windows"><img src="https://travis-ci.org/soonhokong/lean-windows.png?branch=master" title="Windows, x86_64-w64-mingw32-g++-4.8.2"/></a></td>
    <td><a href="https://travis-ci.org/leanprover/lean"><img src="https://travis-ci.org/leanprover/lean.png?branch=master" title="Ubuntu 12.04 LTS 64bit, g++-4.8 | clang++-3.3"/></a></td>
    <td><a href="https://travis-ci.org/soonhokong/lean-osx"><img src="https://travis-ci.org/soonhokong/lean-osx.png?branch=master" title="Mac OS X 10.8.2, g++-4.9"/></a></td>
    <td><a href="https://coveralls.io/r/leanprover/lean?branch=master"><img src="https://coveralls.io/repos/leanprover/lean/badge.png?branch=master"/></a></td>
    <td><a href="http://build.leanprover.net"><img src="https://leanprover.github.io/images/cdash.svg"/></a></td>
    <td><a href="https://scan.coverity.com/projects/2153"><img alt="Coverity Scan Build Status" src="https://scan.coverity.com/projects/2153/badge.svg"/></a></td>
  </tr>
</table>

[![Issue Stats](http://issuestats.com/github/leanprover/lean/badge/pr)](http://issuestats.com/github/leanprover/lean)
[![Issue Stats](http://issuestats.com/github/leanprover/lean/badge/issue)](http://issuestats.com/github/leanprover/lean)

About
-----

- [Homepage](https://leanprover.github.io)
- Theorem Proving in Lean: [HTML](https://leanprover.github.io/tutorial/index.html), [PDF](http://leanprover.github.io/tutorial/tutorial.pdf)
- [Authors](http://leanprover.github.io/people/)
- [Standard Library](library/library.md)
- [HoTT Library](hott/hott.md)
- [Short Tutorial](doc/lean/tutorial.org)
- [To Do list](doc/todo.md)

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

_Windows_

- [MSys2](doc/make/msys2.md)
- [Cygwin](doc/make/cygwin.md)

_Linux_

- [Ubuntu 12.04](doc/make/ubuntu-12.04.md)
- [Ubuntu 12.04 (detailed)](doc/make/ubuntu-12.04-detailed.md)
- [Fedora 19](doc/make/fedora-19.md)

_OS X_

- [OS X 10.9](doc/make/osx-10.9.md)

Build Instructions
------------------

- [CMake + Make](doc/make/cmake_make.md)
- [CMake + Ninja](doc/make/cmake_ninja.md)
- [Faster builds with ccache](doc/make/ccache.md)

Miscellaneous
-------------

- [Testing and Code Coverage](doc/make/coverage.md)
- Building Doxygen Documentation: `doxygen src/Doxyfile`
- [Coding Style](doc/coding_style.md)
- [Git Commit Convention](doc/commit_convention.md)
- [Automatic Builds](doc/make/travis.md)
- [Syntax Highlight Lean Code in LaTeX](doc/syntax_highlight_in_latex.md)
