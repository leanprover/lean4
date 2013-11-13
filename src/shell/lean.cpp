/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <fstream>
#include <signal.h>
#include "util/interrupt.h"
#include "kernel/printer.h"
#include "frontends/lean/parser.h"
#include "bindings/lua/leanlua_state.h"
#include "version.h"

using lean::shell;
using lean::frontend;
using lean::parser;
using lean::leanlua_state;

static void on_ctrl_c(int ) {
    lean::request_interrupt();
}

bool lean_shell() {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    std::cout << "Type Ctrl-D to exit or 'Help.' for help."<< std::endl;
    frontend f;
    leanlua_state S;
    shell sh(f, &S);
    signal(SIGINT, on_ctrl_c);
    return sh();
}

int main(int argc, char ** argv) {
    if (argc == 1) {
        return lean_shell() ? 0 : 1;
    } else {
        bool ok = true;
        frontend f;
        leanlua_state S;
        for (int i = 1; i < argc; i++) {
            std::ifstream in(argv[i]);
            parser p(f, in, &S, false, false);
            if (!p())
                ok = false;
        }
        return ok ? 0 : 1;
    }
}
