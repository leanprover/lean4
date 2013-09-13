Using [CMake][cmake] + Make
---------------------------
Instructions for DEBUG build

    mkdir -p build/debug
    cd build/debug
    cmake -DCMAKE_BUILD_TYPE=DEBUG ../../src
    make

Instructions for RELEASE build

    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_BUILD_TYPE=RELEASE ../../src
    make

[cmake]: http://www.cmake.org/
