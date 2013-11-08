Install Packages on Ubuntu 12.04 LTS
------------------------------------

Instructions for installing gperftools on Ubuntu

    sudo add-apt-repository ppa:agent-8131/ppa
    sudo apt-get update
    sudo apt-get dist-upgrade
    sudo apt-get install libgoogle-perftools-dev

Instructions for installing Lua 5.2
    sudo apt-get install liblua5.2.0 lua5.2-0 lua5.2-dev

Instructions for installing gcc-4.8 (C++11 compatible) on Ubuntu

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo update-alternatives --remove-all gcc
    sudo update-alternatives --remove-all g++
    sudo apt-get update
    sudo apt-get install g++-4.8 -y
    sudo apt-get upgrade -y && sudo apt-get dist-upgrade -y

Instructions for installing clang-3.3 (C++11 compatible) on Ubuntu

    sudo add-apt-repository ppa:h-rayflood/llvm
    sudo apt-get update
    sudo apt-get dist-upgrade
    sudo apt-get install clang-3.3 clang-3.3-doc

Note that you [still need][clang_cxx_status] to have g++-4.8's C++
runtime library to support some C++11 features that we are using.

You can specify the C++ compiler to use by using ``-DCMAKE_CXX_COMPILER``
option. For example

    cmake -DCMAKE_BUILD_TYPE=DEBUG -DCMAKE_CXX_COMPILER=clang++-3.3 ../../src

[clang_cxx_status]: http://clang.llvm.org/cxx_status.html
