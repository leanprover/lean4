Using [CMake][cmake] + [Ninja][ninja]
-------------------------------
[CMake 2.8.11][cmake] supports [Ninja][ninja] build system using
``-G`` option. [Some people report][ninja_work] that using
[Ninja][ninja] can reduce the build time, esp when a build is
incremental.

[ninja_work]: https://plus.google.com/108996039294665965197/posts/SfhrFAhRyyd

Instructions for DEBUG build

    mkdir -p build/debug
    cd build/debug
    cmake -DCMAKE_BUILD_TYPE=DEBUG -G Ninja ../../src
    ninja

Instructions for RELEASE build

    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_BUILD_TYPE=RELEASE -G Ninja ../../src
    ninja

[cmake]: http://www.cmake.org/
[ninja]: http://martine.github.io/ninja/
