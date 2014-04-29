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
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/formatter.h"
#if 0
#include "kernel/io_state.h"
#include "library/printer.h"
#include "library/kernel_bindings.h"
#include "library/io_state_stream.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/shell.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/register_module.h"
#include "frontends/lua/register_modules.h"
#endif
#include "version.h"
#include "githash.h" // NOLINT

using lean::script_state;
using lean::unreachable_reached;

#if 0
using lean::shell;
using lean::parser;
using lean::invoke_debugger;
using lean::notify_assertion_violation;
using lean::environment;
using lean::io_state;
#endif

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
    std::cout << "  --trust -t        trust imported modules\n";
    std::cout << "  --quiet -q        do not print verbose messages\n";
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
    {"nokernel",   no_argument,       0, 'n'},
    {"path",       no_argument,       0, 'p'},
    {"luahook",    required_argument, 0, 'c'},
    {"githash",    no_argument,       0, 'g'},
    {"output",     required_argument, 0, 'o'},
    {"trust",      no_argument,       0, 't'},
    {"quiet",      no_argument,       0, 'q'},
#if defined(LEAN_USE_BOOST)
    {"tstack",     required_argument, 0, 's'},
#endif
    {0, 0, 0, 0}
};

int main(int argc, char ** argv) {
    lean::save_stack_info();
    // lean::register_modules();
    // bool no_kernel      = false;
    // bool export_objects = false;
    // bool trust_imported = false;
    // bool quiet          = false;
    std::string output;
    input_kind default_k = input_kind::Lean; // default
    while (true) {
        int c = getopt_long(argc, argv, "qtnlupgvhc:012s:012o:", g_long_options, NULL);
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
        case 'n':
            // no_kernel = true;
            break;
        case 'o':
            output = optarg;
            // export_objects = true;
            break;
        case 't':
            // trust_imported = true;
            // lean::set_default_trust_imported_for_lua(true);
            break;
        case 'q':
            // quiet = true;
            break;
        default:
            std::cerr << "Unknown command line option\n";
            display_help(std::cerr);
            return 1;
        }
    }

    // environment env;
    // env->set_trusted_imported(trust_imported);
    // io_state ios = init_frontend(env, no_kernel);
    // if (quiet)
    //     ios.set_option("verbose", false);

    script_state S;

    // S.apply([&](lua_State * L) {
    //         set_global_environment(L, env);
    //         set_global_io_state(L, ios);
    //     });

    try {
        if (optind >= argc) {
            display_header(std::cout);
            signal(SIGINT, on_ctrl_c);
            if (default_k == input_kind::Lean) {
#if defined(LEAN_WINDOWS)
                std::cout << "Type 'exit.' to exit or 'help.' for help."<< std::endl;
#else
                std::cout << "Type Ctrl-D or 'exit.' to exit or 'help.' for help."<< std::endl;
#endif
                // shell sh(env, &S);
                // int status = sh() ? 0 : 1;
                // if (export_objects)
                //    env->export_objects(output);
                // return status;
                return 0;
            } else {
                lean_assert(default_k == input_kind::Lua);
                S.import("repl");
                return 0;
            }
        } else {
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
                    // if (!parse_commands(env, ios, argv[i], &S, false, false))
                    //    ok = false;
                } else if (k == input_kind::OLean) {
                    // try {
                    //    env->load(std::string(argv[i]), ios);
                    // } catch (lean::exception & ex) {
                    //    std::cerr << "Failed to load binary file '" << argv[i] << "': " << ex.what() << "\n";
                    //    ok = false;
                    // }
                } else if (k == input_kind::Lua) {
                    try {
                        S.dofile(argv[i]);
                    } catch (lean::exception & ex) {
                        // ::lean::display_error(ios, nullptr, ex);
                        ok = false;
                    }
                } else {
                    lean_unreachable(); // LCOV_EXCL_LINE
                }
            }
            // if (export_objects)
            //    env->export_objects(output);
            return ok ? 0 : 1;
        }
    } catch (lean::exception & ex) {
        // ::lean::display_error(ios, nullptr, ex);
    }
    return 1;
}
