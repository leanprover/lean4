Instructions for Testing and Measuring Code Coverage
====================================================

To measure [code coverage][cover], compile TESTCOV build using g++:

    mkdir -p build/testcov
    cd build/testcov
    cmake -DCMAKE_BUILD_TYPE=TESTCOV -DCMAKE_CXX_COMPILER=g++-4.8 -G Ninja ../../src
    ninja

and run test cases:

    ctest

and collect coverage data using [lcov][lcov] and [gcov][gcov]:

    lcov -c -b ../../src -d . -o cov.info --no-external --gcov-tool gcov-4.8

and generate HTML output:

    genhtml cov.info --output-directory lcov

Note: make sure that the version of ``gcov`` matches with the one of
``g++``. Also try to use the latest ``lcov`` if you have a problem
with the existing one.

[gcov]: http://gcc.gnu.org/onlinedocs/gcc/Gcov.html
[lcov]: http://ltp.sourceforge.net/coverage/lcov.php
[cover]: https://dl.dropboxusercontent.com/u/203889738/lcov/index.html
