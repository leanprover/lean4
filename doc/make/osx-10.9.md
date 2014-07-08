Install Packages on OS X 10.9
-----------------------------
We assume that you are using [homebrew][homebrew], "The missing package manager for OS X".

[homebrew]: http://brew.sh

Instructions for installing gperftools on OS X 10.9

    brew install gperftools

Instructions for installing gcc-4.8.3 (C++11 compatible) on OS X 10.9

    brew install gcc

Instructions for installing clang-3.3 (C++11 compatible) on OS X 10.9

    brew install llvm --with-clang --with-asan

It seems there is a bug in the implementation of `thread_local`
storage specifier on clang++ and g++ on OSX. One possible
workaround is to disable multi threaded support in Lean, we just have to provide
the option

    -D MULTI_THREAD=OFF

to `cmake` when creating Lean's makefiles. This option is simple, but
Lean is use only one core of your system. Another option is to
install Boost and provide the option

    -D BOOST=ON

to `cmake`. This option forces Lean to use the Boost thread library
instead of the standard one. To install Boost, we should use the following command

    brew install boost --c++11

Note that, we have to say we want the C++11 compatible version.
