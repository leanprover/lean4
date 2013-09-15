Install Packages on OS X 10.8
-----------------------------
We assume that you are using [homebrew][homebrew], "The missing package manager for OS X".

[homebrew]: http://brew.sh

Instructions for installing gperftools on OS X 10.8

    brew install gperftools

Instructions for installing gcc-4.8 (C++11 compatible) on OS X 10.8

    brew tap homebrew/versions
    brew install gcc48

Instructions for installing clang-3.3 (C++11 compatible) on OS X 10.8

    brew install llvm --with-clang --with-asan
