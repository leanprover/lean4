Installing Lean on Ubuntu 16.04
---------------------------------------------

### Basic packages

    sudo apt-get install git libgmp-dev libmpfr-dev cmake

### Optional packages

    sudo apt-get install gitg valgrind doxygen kcachegrind

### Clone Lean repository

    git clone https://github.com/leanprover/lean.git

### Build Lean

    cd lean
    mkdir -p build/release
    cd build/release
    cmake ../../src
    make
