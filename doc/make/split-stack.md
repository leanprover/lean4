Compiling Lean with Split Stacks
================================

[Split stacks](http://gcc.gnu.org/wiki/SplitStacks) is a relatively
new feature in gcc.  It allows the stack to grown automatically as
needed.  There is a small performance penalty since the program stack
is stored in the heap. However, we can have multiple threads, each starting
with a small stack, and have the stack grow and shrink as required by
the program.

In principle, it is possible to build a program that uses split-stacks
with libraries that do not. However, it did not work in our experiments.
To be able to compile Lean with split-stacks, we also have to compile
GMP, MPFR using split-stacks.

We also had to use the [gold linker](<http://en.wikipedia.org/wiki/Gold_(linker)>).

Gold linker
-----------

The gold linker is called `ld.gold` (in our test system). On Ubuntu, you
can install it by executing

    sudo apt-get install binutils-gold

Before we compiled GMP, MPFR, and Lean, we created an alias

    alias ld=ld.gold

If everything is working correctly, when we execute `ld --version`, we should
get an output like the following one:

    GNU gold (GNU Binutils for Ubuntu 2.22) 1.11
    Copyright 2011 Free Software Foundation, Inc.
    ...

Compiling GMP using split-stacks
--------------------------------

Download GMP from [https://gmplib.org](https://gmplib.org/); uncompress the gmp tar-ball at `$HOME/tools`; and configure it using

      ./configure CFLAGS=-fsplit-stack --prefix=$HOME/tools/split-stack --enable-static

Then, build and install using

      make
      make install

We should have the file `libgmp.a` at `$HOME/tools/split-stack/lib`.

Compiling Lean using split-stacks
--------------------------------

Go to the Lean directory, and create the folder `build/release`

      mkdir build/release

Configure Lean using

      cmake -D CMAKE_BUILD_TYPE=Release -D CMAKE_CXX_COMPILER=g++ -D TCMALLOC=OFF -D GMP_INCLUDE_DIR=$HOME/tools/split-stack/include -D GMP_LIBRARIES=$HOME/tools/split-stack/lib/libgmp.a ../../src

Remark: if you have ninja build tool installed in your system, you can also provide `-G Ninja`

Then, build using

      make

and, test it

      yes "C" | ctest

The Lean executable will be located at `build/release/shell/lean`.
