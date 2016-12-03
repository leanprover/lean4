<p align=center><a href="https://leanprover.github.io"><img src="https://leanprover.github.io/images/lean_logo.svg" alt="logo" width="300px"/></a></p>
<table>
  <tr>
    <th>License</th><th>Windows</th><th>Linux / macOS</th><th>Test Coverage</th>
  </tr>
  <tr>
    <td><a href="LICENSE"><img src="https://img.shields.io/badge/license-APACHE_2-green.svg?dummy" title="License"/></a></td>
    <td><a href="https://ci.appveyor.com/project/leodemoura/lean"><img src="https://ci.appveyor.com/api/projects/status/github/leodemoura/lean?branch=ci_fixes"/></a></td>
    <td><a href="https://travis-ci.org/leanprover/lean"><img src="https://travis-ci.org/leanprover/lean.png?branch=master"/></a></td>
    <td><a href="https://codecov.io/gh/leanprover/lean"><img src="https://codecov.io/gh/leanprover/lean/branch/master/graph/badge.svg" alt="Codecov"/></a></td>
  </tr>
</table>

[![Issue Stats](http://issuestats.com/github/leanprover/lean/badge/pr)](http://issuestats.com/github/leanprover/lean)

About
-----

- [Homepage](http://leanprover.github.io)
- [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/index.html)
- [Standard Library](library/library.md)
- [Emacs Mode](src/emacs/README.md)
- [Short Tutorial](doc/lean/tutorial.org)
- For HoTT mode, please use [Lean2](https://github.com/leanprover/lean2).

Requirements
------------

- C++11 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)
- [MPFR (GNU MPFR Library)](http://www.mpfr.org/)
- (optional) [gperftools](https://code.google.com/p/gperftools/)
- (optional) [Boost](http://www.boost.org) (version >= 1.54), we can
  build Lean using boost::thread instead of std::thread. When using
  Boost, Lean can modify the thread stack size.

Installing required packages at
--------------------------------

_Windows_

- [MSys2](doc/make/msys2.md)

_Linux_

- [Ubuntu 16.04](doc/make/ubuntu-16.04.md)

_OS X_

- [OS X 10.9](doc/make/osx-10.9.md)

Build Instructions
------------------

- [CMake + Make](doc/make/cmake_make.md)
- [CMake + Ninja](doc/make/cmake_ninja.md)
- [Faster builds with ccache](doc/make/ccache.md)

Miscellaneous
-------------

- Building Doxygen Documentation: `doxygen src/Doxyfile`
- [Coding Style](doc/coding_style.md)
- [Library Style Conventions](doc/lean/library_style.org)
- [Git Commit Conventions](doc/commit_convention.md)
- [Automatic Builds](doc/make/travis.md)
- [Syntax Highlight Lean Code in LaTeX](doc/syntax_highlight_in_latex.md)
