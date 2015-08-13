/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "init/init.h"

int main() {
    lean::initializer init;
    lean::environment env;
    std::cout << "Lean (empty) environment was successfully created\n";
    return 0;
}
