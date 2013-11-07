/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/exception.h"
#include "bindings/lua/leanlua_state.h"

int main(int argc, char ** argv) {
    lean::leanlua_state S;
    int exitcode = 0;

    for (int i = 1; i < argc; i++) {
        try {
            S.dofile(argv[i]);
        } catch (lean::exception & ex) {
            std::cerr << ex.what() << std::endl;
            exitcode = 1;
        }
    }
    return exitcode;
}
