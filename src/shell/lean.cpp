/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <fstream>
#include <signal.h>
#include <cstdlib>
#include <getopt.h>
#include <string>
#include "util/stackinfo.h"
#include "util/debug.h"
#include "util/interrupt.h"
#include "util/script_state.h"
#include "util/thread.h"
#include "util/lean_path.h"
#include "kernel/printer.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/kernel_bindings.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/frontend.h"
#include "frontends/lua/register_modules.h"
#include "shell/lua_repl.h"
#include "version.h"
#include "githash.h" // NOLINT

using lean::shell;
using lean::parser;
using lean::script_state;
using lean::unreachable_reached;
using lean::invoke_debugger;
using lean::notify_assertion_violation;
using lean::environment;
using lean::io_state;

enum class input_kind { Unspecified, Lean, OLean, Lua };

static void on_ctrl_c(int ) {
    lean::request_interrupt();
}

static void display_header(std::ostream & out) {
    out << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ", commit " << std::string(g_githash).substr(0, 12) << ")\n";
}

static void display_help(std::ostream & out) {
    display_header(out);
    std::cout << "Input format:\n";
    std::cout << "  --lean            use parser for Lean default input format for files,\n";
    std::cout << "                    with unknown extension (default)\n";
    std::cout << "  --olean           use parser for Lean binary input format for files\n";
    std::cout << "                    with unknown extension\n";
    std::cout << "  --lua             use Lua parser for files with unknown extension\n";
    std::cout << "Miscellaneous:\n";
    std::cout << "  --help -h         display this message\n";
    std::cout << "  --version -v      display version number\n";
    std::cout << "  --githash         display the git commit hash number used to build this binary\n";
    std::cout << "  --path            display the path used for finding Lean libraries and extensions\n";
    std::cout << "  --output=file -o  save the final environment in binary format in the given file\n";
    std::cout << "  --luahook=num -c  how often the Lua interpreter checks the interrupted flag,\n";
    std::cout << "                    it is useful for interrupting non-terminating user scripts,\n";
    std::cout << "                    0 means 'do not check'.\n";
#if defined(LEAN_USE_BOOST)
    std::cout << "  --tstack=num -s   thread stack size in Kb\n";
#endif
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

static struct option g_long_options[] = {
    {"version",    no_argument,       0, 'v'},
    {"help",       no_argument,       0, 'h'},
    {"lean",       no_argument,       0, 'l'},
    {"olean",      no_argument,       0, 'b'},
    {"lua",        no_argument,       0, 'u'},
    {"path",       no_argument,       0, 'p'},
    {"luahook",    required_argument, 0, 'c'},
    {"githash",    no_argument,       0, 'g'},
    {"output",     required_argument, 0, 'o'},
#if defined(LEAN_USE_BOOST)
    {"tstack",     required_argument, 0, 's'},
#endif
    {0, 0, 0, 0}
};

int main(int argc, char ** argv) {
    lean::save_stack_info();
    lean::register_modules();
    bool export_objects = false;
    std::string output;
    input_kind default_k = input_kind::Lean; // default
    while (true) {
        int c = getopt_long(argc, argv, "lupgvhc:012s:012o:", g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        switch (c) {
        case 'v':
            display_header(std::cout);
            return 0;
        case 'g':
            std::cout << g_githash << "\n";
            return 0;
        case 'h':
            display_help(std::cout);
            return 0;
        case 'l':
            default_k = input_kind::Lean;
            break;
        case 'u':
            default_k = input_kind::Lua;
            break;
        case 'b':
            default_k = input_kind::OLean;
            break;
        case 'c':
            script_state::set_check_interrupt_freq(atoi(optarg));
            break;
        case 'p':
            std::cout << lean::get_lean_path() << "\n";
            return 0;
        case 's':
            lean::set_thread_stack_size(atoi(optarg)*1024);
            break;
        case 'o':
            output = optarg;
            export_objects = true;
            break;
        default:
            std::cerr << "Unknown command line option\n";
            display_help(std::cerr);
            return 1;
        }
    }
    if (optind >= argc) {
        display_header(std::cout);
        signal(SIGINT, on_ctrl_c);
        if (default_k == input_kind::Lean) {
            #if defined(LEAN_WINDOWS)
            std::cout << "Type 'Exit.' to exit or 'Help.' for help."<< std::endl;
            #else
            std::cout << "Type Ctrl-D or 'Exit.' to exit or 'Help.' for help."<< std::endl;
            #endif
            environment env;
            io_state ios;
            init_frontend(env, ios);
            script_state S;
            shell sh(env, &S);
            int status = sh() ? 0 : 1;
            if (export_objects)
                env->export_objects(output);
            return status;
        } else {
            lean_assert(default_k == input_kind::Lua);
            script_state S;
            S.dostring(g_lua_repl);
        }
    } else {
        environment env;
        io_state    ios;
        init_frontend(env, ios);
        script_state S;
        bool ok = true;
        for (int i = optind; i < argc; i++) {
            char const * ext = get_file_extension(argv[i]);
            input_kind k     = default_k;
            if (ext) {
                if (strcmp(ext, "lean") == 0) {
                    k = input_kind::Lean;
                } else if (strcmp(ext, "olean") == 0) {
                    k = input_kind::OLean;
                } else if (strcmp(ext, "lua") == 0) {
                    k = input_kind::Lua;
                }
            }
            if (k == input_kind::Lean) {
                std::ifstream in(argv[i]);
                if (in.bad() || in.fail()) {
                    std::cerr << "Failed to open file '" << argv[i] << "'\n";
                    return 1;
                }
                if (!parse_commands(env, ios, in, &S, false, false))
                    ok = false;
            } else if (k == input_kind::OLean) {
                try {
                    env->load(std::string(argv[i]), ios);
                } catch (lean::exception & ex) {
                    std::cerr << "Failed to load binary file '" << argv[i] << "': " << ex.what() << "\n";
                    ok = false;
                }
            } else if (k == input_kind::Lua) {
                try {
                    S.dofile(argv[i]);
                } catch (lean::exception & ex) {
                    std::cerr << ex.what() << std::endl;
                    ok = false;
                }
            } else {
                lean_unreachable(); // LCOV_EXCL_LINE
            }
        }
        if (export_objects)
            env->export_objects(output);
        return ok ? 0 : 1;
    }
}
