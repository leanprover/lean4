/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <fstream>
#include <signal.h>
#include <getopt.h>
#include "util/interrupt.h"
#include "kernel/printer.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/frontend.h"
#include "bindings/lua/leanlua_state.h"
#include "version.h"

using lean::shell;
using lean::frontend;
using lean::parser;
using lean::leanlua_state;

enum class input_kind { Unspecified, Lean, Lua };

struct option long_options[] = {
    {"version", no_argument,       0, 'v'},
    {"help",    no_argument,       0, 'h'},
    {"lean",    no_argument,       0, 0},
    {"lua",     no_argument,       0, 0},
    {0, 0, 0, 0}
};

static void on_ctrl_c(int ) {
    lean::request_interrupt();
}

static char const * get_file_extension(char const * fname) {
    if (fname == 0)
        return 0;
    char const * last_dot = 0;
    while (true) {
        char const * tmp = strchr(fname, '.');
        if (tmp == 0) {
            return last_dot;
        }
        last_dot  = tmp + 1;
        fname = last_dot;
    }
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
            input_kind k = input_kind::Unspecified;
            char const * ext = get_file_extension(argv[i]);
            if (ext) {
                if (strcmp(ext, "lean") == 0) {
                    k = input_kind::Lean;
                } else if (strcmp(ext, "lua") == 0) {
                    k = input_kind::Lua;
                }
            }
            if (k == input_kind::Unspecified) {
                // assume the input is in Lean format
                k = input_kind::Lean;
            }

            if (k == input_kind::Lean) {
                std::ifstream in(argv[i]);
                parser p(f, in, &S, false, false);
                if (!p())
                    ok = false;
            } else if (k == input_kind::Lua) {
                try {
                    S.dofile(argv[i]);
                } catch (lean::exception & ex) {
                    std::cerr << ex.what() << std::endl;
                    ok = false;
                }
            }
        }
        return ok ? 0 : 1;
    }
}
