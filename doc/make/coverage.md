Instructions for Testing and Measuring Code Coverage
====================================================

To measure code coverage, compile TESTCOV build using g++:

    mkdir -p build/testcov
    cd build/testcov
    cmake -DCMAKE_BUILD_TYPE=Debug -DTESTCOV=ON -DCMAKE_CXX_COMPILER=g++-4.8 -G Ninja ../../src

and run:

    ninja cov
    
It will build the project, run testcases, and compute code-coverage. 
In the end, you have ``build/testcov/coverage`` directory containing
a code-coverage report in HTML format.

Note: make sure that the version of ``gcov`` matches with the one of
``g++``. Also try to use the latest ``lcov`` if you have a problem
with the existing one.

[gcov]: http://gcc.gnu.org/onlinedocs/gcc/Gcov.html
[lcov]: http://ltp.sourceforge.net/coverage/lcov.php
