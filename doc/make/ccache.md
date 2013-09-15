Using ccache
------------

[ccache](http://ccache.samba.org/manual.html) is available in many
systems, and can dramatically improve compilation times. In particular
if we are constantly switching between different branches.

On Ubuntu, we can install ccache by executing

    sudo apt-get install ccache

Then, we can create a simple script that invokes ccache with our
favorite C++ 11 compiler. For example, we can create the script
`~/bin/ccache-g++` with the following content:

    #!/bin/sh
    ccache g++ "$@"

Then, we instruct cmake to use `ccache-g++` as our C++ compiler

    cmake -D CMAKE_BUILD_TYPE=Debug -D CMAKE_CXX_COMPILER=~/bin/ccache-g++ ../../src

We usually use Ninja instead of make. Thus, our cmake command
line is:

    cmake -D CMAKE_BUILD_TYPE=Debug -D CMAKE_CXX_COMPILER=~/bin/ccache-g++ -G Ninja ../../src
