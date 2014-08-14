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
#include "util/thread_script_state.h"
#include "util/lean_path.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/formatter.h"
#include "library/standard_kernel.h"
#include "library/hott_kernel.h"
#include "library/module.h"
#include "library/io_state_stream.h"
#include "library/definitions_cache.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/server.h"
#include "frontends/lean/dependencies.h"
#include "frontends/lua/register_modules.h"
#include "version.h"
#include "githash.h" // NOLINT

using lean::script_state;
using lean::unreachable_reached;
using lean::environment;
using lean::io_state;
using lean::io_state_stream;
using lean::regular;
using lean::mk_environment;
using lean::mk_hott_environment;
using lean::set_environment;
using lean::set_io_state;
using lean::definitions_cache;
using lean::pos_info;
using lean::pos_info_provider;
using lean::optional;
using lean::expr;

enum class input_kind { Unspecified, Lean, Lua };

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
    std::cout << "  --lua             use Lua parser for files with unknown extension\n";
    std::cout << "Miscellaneous:\n";
    std::cout << "  --help -h         display this message\n";
    std::cout << "  --version -v      display version number\n";
    std::cout << "  --githash         display the git commit hash number used to build this binary\n";
    std::cout << "  --path            display the path used for finding Lean libraries and extensions\n";
    std::cout << "  --output=file -o  save the final environment in binary format in the given file\n";
    std::cout << "  --luahook=num -k  how often the Lua interpreter checks the interrupted flag,\n";
    std::cout << "                    it is useful for interrupting non-terminating user scripts,\n";
    std::cout << "                    0 means 'do not check'.\n";
    std::cout << "  --trust=num -t    trust level (default: 0) \n";
    std::cout << "  --quiet -q        do not print verbose messages\n";
    std::cout << "  --server          start Lean in 'server' mode\n";
    std::cout << "  --hott            use Homotopy Type Theory kernel and libraries\n";
    std::cout << "  --threads=num -j  number of threads used to process lean files\n";
    std::cout << "  --deps            just print dependencies of a Lean input\n";
    std::cout << "  --flycheck        print structured error message for flycheck\n";
    std::cout << "  --cache=file -c   load/save cached definitions from/to the given file\n";
    std::cout << "  --permissive -P   save .olean files even when errors were found\n";
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
    {"version",     no_argument,       0, 'v'},
    {"help",        no_argument,       0, 'h'},
    {"lean",        no_argument,       0, 'l'},
    {"lua",         no_argument,       0, 'u'},
    {"path",        no_argument,       0, 'p'},
    {"luahook",     required_argument, 0, 'k'},
    {"githash",     no_argument,       0, 'g'},
    {"output",      required_argument, 0, 'o'},
    {"trust",       required_argument, 0, 't'},
    {"server",      no_argument,       0, 'S'},
    {"quiet",       no_argument,       0, 'q'},
    {"hott",        no_argument,       0, 'H'},
    {"threads",     required_argument, 0, 'j'},
    {"cache",       required_argument, 0, 'c'},
    {"deps",        no_argument,       0, 'D'},
    {"flycheck",    no_argument,       0, 'F'},
    {"permissive",  no_argument,       0, 'P'},
#if defined(LEAN_USE_BOOST)
    {"tstack",      required_argument, 0, 's'},
#endif
    {0, 0, 0, 0}
};

#if defined(LEAN_USE_BOOST)
static char const * g_opt_str = "PFDHSqlupgvhj:012k:012s:012t:012o:c:";
#else
static char const * g_opt_str = "PFDHSqlupgvhj:012k:012t:012o:c:";
#endif

enum class lean_mode { Standard, HoTT };

class simple_pos_info_provider : public pos_info_provider {
    char const * m_fname;
public:
    simple_pos_info_provider(char const * fname):m_fname(fname) {}
    virtual optional<pos_info> get_pos_info(expr const &) const { return optional<pos_info>(); }
    virtual char const * get_file_name() const { return m_fname; }
    virtual pos_info get_some_pos() const { return pos_info(-1, -1); }
};

int main(int argc, char ** argv) {
    lean::save_stack_info();
    lean::register_modules();
    bool export_objects  = false;
    unsigned trust_lvl   = 0;
    bool quiet           = false;
    bool server          = false;
    bool only_deps       = false;
    bool flycheck        = false;
    bool permissive      = false;
    lean_mode mode       = lean_mode::Standard;
    unsigned num_threads = 1;
    bool use_cache       = false;
    std::string output;
    std::string cache_name;
    input_kind default_k = input_kind::Lean; // default
    while (true) {
        int c = getopt_long(argc, argv, g_opt_str, g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        switch (c) {
        case 'j':
            num_threads = atoi(optarg);
            break;
        case 'H':
            mode = lean_mode::HoTT;
            lean::init_lean_path("hott");
            break;
        case 'S':
            server = true;
            break;
        case 'P':
            permissive = true;
            break;
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
        case 'k':
            script_state::set_check_interrupt_freq(atoi(optarg));
            break;
        case 'p':
            std::cout << lean::get_lean_path() << "\n";
            return 0;
        case 's':
            lean::set_thread_stack_size(atoi(optarg)*1024);
            break;
        case 'o':
            output         = optarg;
            export_objects = true;
            break;
        case 'c':
            cache_name = optarg;
            use_cache  = true;
            break;
        case 't':
            trust_lvl = atoi(optarg);
            break;
        case 'q':
            quiet = true;
            break;
        case 'D':
            only_deps = true;
            break;
        case 'F':
            flycheck = true;
            break;
        default:
            std::cerr << "Unknown command line option\n";
            display_help(std::cerr);
            return 1;
        }
    }

    environment env = mode == lean_mode::Standard ? mk_environment(trust_lvl) : mk_hott_environment(trust_lvl);
    io_state ios(lean::mk_pretty_formatter_factory());
    if (quiet)
        ios.set_option("verbose", false);
    if (flycheck)
        ios.set_option("flycheck", true);
    script_state S = lean::get_thread_script_state();
    set_environment set1(S, env);
    set_io_state    set2(S, ios);
    definitions_cache   cache;
    definitions_cache * cache_ptr = nullptr;
    if (use_cache) {
        cache_ptr = &cache;
        std::ifstream in(cache_name);
        if (!in.bad() && !in.fail())
            cache.load(in);
    }

    try {
        bool ok = true;
        for (int i = optind; i < argc; i++) {
            try {
                char const * ext = get_file_extension(argv[i]);
                input_kind k     = default_k;
                if (ext) {
                    if (strcmp(ext, "lean") == 0) {
                        k = input_kind::Lean;
                    } else if (strcmp(ext, "lua") == 0) {
                        k = input_kind::Lua;
                    }
                }
                if (k == input_kind::Lean) {
                    if (only_deps) {
                        display_deps(env, std::cout, argv[i]);
                    } else if (!parse_commands(env, ios, argv[i], false, num_threads, cache_ptr)) {
                        ok = false;
                    }
                } else if (k == input_kind::Lua) {
                    lean::system_import(argv[i]);
                } else {
                    lean_unreachable(); // LCOV_EXCL_LINE
                }
            } catch (lean::exception & ex) {
                simple_pos_info_provider pp(argv[i]);
                ok = false;
                lean::display_error(diagnostic(env, ios), &pp, ex);
            }
        }
        if (ok && server && default_k == input_kind::Lean) {
            signal(SIGINT, on_ctrl_c);
            lean::server Sv(env, ios, num_threads);
            if (!Sv(std::cin))
                ok = false;
        }
        if (use_cache) {
            std::ofstream out(cache_name, std::ofstream::binary);
            cache.save(out);
        }
        if (export_objects && (permissive || ok)) {
            std::ofstream out(output, std::ofstream::binary);
            export_module(out, env);
        }
        return ok ? 0 : 1;
    } catch (lean::exception & ex) {
        lean::display_error(diagnostic(env, ios), nullptr, ex);
    }
    return 1;
}
