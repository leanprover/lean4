Using ccache
============

[ccache](http://ccache.samba.org/manual.html) is available in many
systems, and can dramatically improve compilation times. In particular
if we are constantly switching between different branches.

On Ubuntu, we can install ccache by executing

    sudo apt-get install ccache

Using ccache with g++
---------------------

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

Using ccache with clang++
-------------------------

To use ccache with clang++, create the script ``~/bin/ccache-clang++``
with the following content:

    #!/bin/sh
    ccache clang++ -Qunused-arguments -fcolor-diagnostics "$@"

 - ``-Qunused-arguments`` option is used to suppress "clang: warning:
   argument unused during compilation:" warning.
 - ``-fcolor-diagnostics`` option is used to enable clang's colored
   diagnostic messages.

Reference: http://petereisentraut.blogspot.com/2011/05/ccache-and-clang.html
