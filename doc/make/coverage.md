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

Make sure that the version of ``gcov`` matches with the one of
``g++``. Also try to use the latest ``lcov`` (currently lcov-1.10)
if you have a problem with the existing one:

    wget http://downloads.sourceforge.net/ltp/lcov-1.10.tar.gz;
    tar xvfz lcov-1.10.tar.gz;
    cp -v lcov-1.10/bin/{lcov,genpng,gendesc,genhtml,geninfo} /usr/bin/;
    rm -rf lcov-1.10.tar.gz lcov-1.10;

[gcov]: http://gcc.gnu.org/onlinedocs/gcc/Gcov.html
[lcov]: http://ltp.sourceforge.net/coverage/lcov.php
