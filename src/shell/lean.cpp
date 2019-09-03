/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <fstream>
#include <signal.h>
#include <cctype>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>
#include <set>
#include "runtime/stackinfo.h"
#include "runtime/interrupt.h"
#include "runtime/memory.h"
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/sstream.h"
#include "util/timer.h"
#include "util/macros.h"
#include "util/io.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "util/options.h"
#include "util/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "library/formatter.h"
#include "library/module.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"
#include "library/message_builder.h"
#include "library/time_task.h"
#include "library/private.h"
#include "library/compiler/ir.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/json.h"
#include "frontends/lean/util.h"
#include "library/trace.h"
#include "init/init.h"
#include "frontends/lean/simple_pos_info_provider.h"
#include "library/compiler/ir_interpreter.h"
#ifdef _MSC_VER
#include <io.h>
#define STDOUT_FILENO 1
#else
#include <getopt.h>
#include <unistd.h>
#endif
#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#endif
#include "githash.h" // NOLINT

#if defined(LEAN_LLVM)
#include <llvm/Support/TargetSelect.h>
#endif

#ifdef _MSC_VER
// extremely simple implementation of getopt.h
enum arg_opt { no_argument, required_argument, optional_argument };

struct option {
    const char name[12];
    arg_opt has_arg;
    int *flag;
    char val;
};

static char *optarg;
static int optind = 1;

int getopt_long(int argc, char *in_argv[], const char *optstring, const option *opts, int *index) {
    optarg = nullptr;
    if (optind >= argc)
        return -1;

    char *argv = in_argv[optind];
    if (argv[0] != '-') {
        // find first -opt if any
        int i = optind;
        bool found = false;
        for (; i < argc; ++i) {
            if (in_argv[i][0] == '-') {
                found = true;
                break;
            }
        }
        if (!found)
            return -1;
        auto next = in_argv[i];
        // FIXME: this doesn't account for long options with arguments like --foo arg
        memmove(&in_argv[optind + 1], &in_argv[optind], (i - optind) * sizeof(argv));
        argv = in_argv[optind] = next;
    }
    ++optind;

    // long option
    if (argv[1] == '-') {
        auto eq = strchr(argv, '=');
        size_t sz = (eq ? (eq - argv) : strlen(argv)) - 2;
        for (auto I = opts; *I->name; ++I) {
            if (!strncmp(I->name, argv + 2, sz) && I->name[sz] == '\0') {
                assert(!I->flag);
                switch (I->has_arg) {
                case no_argument:
                    if (eq) {
                        std::cerr << in_argv[0] << ": option doesn't take an argument -- " << I->name << std::endl;
                        return '?';
                    }
                    break;
                case required_argument:
                    if (eq) {
                        optarg = eq + 1;
                    } else {
                        if (optind >= argc) {
                            std::cerr << in_argv[0] << ": option requires an argument -- " << I->name << std::endl;
                            return '?';
                        }
                        optarg = in_argv[optind++];
                    }
                    break;
                case optional_argument:
                    if (eq) {
                        optarg = eq + 1;
                    }
                    break;
                }
                if (index)
                  *index = I - opts;
                return I->val;
            }
        }
        return '?';
    } else {
        auto opt = strchr(optstring, argv[1]);
        if (!opt)
            return '?';

        if (opt[1] == ':') {
            if (argv[2] == '\0') {
                if (optind < argc) {
                    optarg = in_argv[optind++];
                } else {
                    std::cerr << in_argv[0] << ": option requires an argument -- " << *opt << std::endl;
                    return '?';
                }
            } else {
                optarg = argv + 2;
            }
        }
        return *opt;
    }
}
#endif

using namespace lean; // NOLINT

// object * lean_process_file(object * filename, object * contents, uint8 json, object * env, object * world);

#ifndef LEAN_SERVER_DEFAULT_MAX_MEMORY
#define LEAN_SERVER_DEFAULT_MAX_MEMORY 1024
#endif
#ifndef LEAN_DEFAULT_MAX_MEMORY
#define LEAN_DEFAULT_MAX_MEMORY 0
#endif
#ifndef LEAN_DEFAULT_MAX_HEARTBEAT
#define LEAN_DEFAULT_MAX_HEARTBEAT 0
#endif
#ifndef LEAN_SERVER_DEFAULT_MAX_HEARTBEAT
#define LEAN_SERVER_DEFAULT_MAX_HEARTBEAT 100000
#endif

static void display_header(std::ostream & out) {
    out << "Lean (version " << get_version_string() << ", " << LEAN_STR(LEAN_BUILD_TYPE) << ")\n";
}

static void display_help(std::ostream & out) {
    display_header(out);
    std::cout << "Miscellaneous:\n";
    std::cout << "  --help -h          display this message\n";
    std::cout << "  --version -v       display version number\n";
    std::cout << "  --githash          display the git commit hash number used to build this binary\n";
    std::cout << "  --run              executes the 'main' definition\n";
    std::cout << "  --make             create olean file\n";
    std::cout << "  --cpp=fname -c     name of the C++ output file\n"; // TODO(Leo): delete
    std::cout << "  --c=fname -C       name of the C output file\n";
    std::cout << "  --stdin            take input from stdin\n";
    std::cout << "  --trust=num -t     trust level (default: max) 0 means do not trust any macro,\n"
              << "                     and type check all imported modules\n";
    std::cout << "  --quiet -q         do not print verbose messages\n";
    std::cout << "  --memory=num -M    maximum amount of memory that should be used by Lean\n";
    std::cout << "                     (in megabytes)\n";
    std::cout << "  --timeout=num -T   maximum number of memory allocations per task\n";
    std::cout << "                     this is a deterministic way of interrupting long running tasks\n";
#if defined(LEAN_MULTI_THREAD)
    std::cout << "  --threads=num -j   number of threads used to process lean files\n";
    std::cout << "  --tstack=num -s    thread stack size in Kb\n";
#endif
    std::cout << "  --deps             just print dependencies of a Lean input\n";
#if defined(LEAN_JSON)
    std::cout << "  --json             print JSON-formatted structured error messages\n";
    std::cout << "  --server           start lean in server mode\n";
    std::cout << "  --server=file      start lean in server mode, redirecting standard input from the specified file (for debugging)\n";
#endif
    std::cout << "  --new-frontend     use new frontend\n";
    std::cout << "  --profile          display elaboration/type checking time for each definition/theorem\n";
    std::cout << "  --stats            display environment statistics\n";
    DEBUG_CODE(
    std::cout << "  --debug=tag        enable assertions with the given tag\n";
        )
    std::cout << "  -D name=value      set a configuration option (see set_option command)\n";
}

static struct option g_long_options[] = {
    {"version",      no_argument,       0, 'v'},
    {"help",         no_argument,       0, 'h'},
    {"githash",      no_argument,       0, 'g'},
    {"run",          no_argument,       0, 'r'},
    {"make",         no_argument,       0, 'm'},
    {"stdin",        no_argument,       0, 'i'},
    {"memory",       required_argument, 0, 'M'},
    {"trust",        required_argument, 0, 't'},
    {"profile",      no_argument,       0, 'P'},
    {"stats",        no_argument,       0, 'a'},
    {"threads",      required_argument, 0, 'j'},
    {"quiet",        no_argument,       0, 'q'},
    {"deps",         no_argument,       0, 'd'},
    {"timeout",      optional_argument, 0, 'T'},
    {"cpp",          optional_argument, 0, 'c'},
    {"c",            optional_argument, 0, 'C'},
#if defined(LEAN_JSON)
    {"json",         no_argument,       0, 'J'},
    {"server",       optional_argument, 0, 'S'},
#endif
    {"new-frontend", optional_argument, 0, 'n'},
#if defined(LEAN_MULTI_THREAD)
    {"tstack",       required_argument, 0, 's'},
#endif
#ifdef LEAN_DEBUG
    {"debug",        required_argument, 0, 'B'},
#endif
    {0, 0, 0, 0}
};

static char const * g_opt_str =
    "PdD:c:C:qgvht:012j:012rM:012T:012a"
#if defined(LEAN_MULTI_THREAD)
    "s:012"
#endif
; // NOLINT

options set_config_option(options const & opts, char const * in) {
    if (!in) return opts;
    while (*in && std::isspace(*in))
        ++in;
    std::string in_str(in);
    auto pos = in_str.find('=');
    if (pos == std::string::npos)
        throw lean::exception("invalid -D parameter, argument must contain '='");
    lean::name opt = lean::string_to_name(in_str.substr(0, pos));
    std::string val = in_str.substr(pos+1);
    auto decls = lean::get_option_declarations();
    auto it = decls.find(opt);
    if (it) {
        switch (it->kind()) {
        case lean::data_value_kind::Bool:
            if (val == "true")
                return opts.update(opt, true);
            else if (val == "false")
                return opts.update(opt, false);
            else
                throw lean::exception(lean::sstream() << "invalid -D parameter, invalid configuration option '" << opt
                                      << "' value, it must be true/false");
        case lean::data_value_kind::Nat:
            return opts.update(opt, static_cast<unsigned>(atoi(val.c_str())));
        case lean::data_value_kind::String:
            return opts.update(opt, val.c_str());
        default:
            throw lean::exception(lean::sstream() << "invalid -D parameter, configuration option '" << opt
                                  << "' cannot be set in the command line, use set_option command");
        }
    } else {
        throw lean::exception(lean::sstream() << "invalid -D parameter, unknown configuration option '" << opt << "'");
    }
}

class initializer {
private:
    lean::initializer m_init;
public:
    initializer() {
    }
    ~initializer() {
    }
};

namespace lean {
extern "C" object* lean_test_module_parser(object* env, object* input, object* filename, uint8 displayCtx, object* w);
bool test_module_parser(environment const & env, std::string const & input, std::string const & filename) {
    return get_io_scalar_result<bool>(lean_test_module_parser(env.to_obj_arg(), mk_string(input), mk_string(filename), false, io_mk_world()));
}

extern "C" object* lean_init_search_path(object* opt_path, object* w);

void init_search_path() {
    get_io_scalar_result<unsigned>(lean_init_search_path(mk_option_none(), io_mk_world()));
}

extern "C" object* lean_find_lean(object* mod_name, object* w);

std::string find_lean_file(name mod_name) {
    string_ref fname = get_io_result<string_ref>(lean_find_lean(mod_name.to_obj_arg(), io_mk_world()));
    return fname.to_std_string();
}

extern "C" object* lean_module_name_of_file(object* fname, object* w);

name module_name_of_file2(std::string const & fname) {
    return get_io_result<name>(lean_module_name_of_file(mk_string(fname), io_mk_world()));
}
}

int main(int argc, char ** argv) {
#if defined(LEAN_EMSCRIPTEN)
    EM_ASM(
        var lean_path = process.env['LEAN_PATH'];
        if (lean_path) {
            ENV['LEAN_PATH'] = lean_path;
        }

        try {
            // emscripten cannot mount all of / in the vfs,
            // we can only mount subdirectories...
            FS.mount(NODEFS, { root: '/home' }, '/home');
            FS.mkdir('/root');
            FS.mount(NODEFS, { root: '/root' }, '/root');

            FS.chdir(process.cwd());
        } catch (e) {
            console.log(e);
        });
#endif
    auto init_start = std::chrono::steady_clock::now();
    ::initializer init;
    second_duration init_time = std::chrono::steady_clock::now() - init_start;
    bool run = false;
    bool make_mode = false;
    bool use_stdin = false;
    unsigned trust_lvl = LEAN_BELIEVER_TRUST_LEVEL + 1;
    bool only_deps = false;
    bool new_frontend = false;
    bool stats = false;
    // unsigned num_threads    = 0;
#if defined(LEAN_MULTI_THREAD)
    // num_threads = hardware_concurrency();
#endif
#if defined(LEAN_JSON)
    bool json_output = false;
#endif
#if defined(LEAN_LLVM)
    // Initialize LLVM backends for native code generation.
    llvm::InitializeNativeTarget();
#endif

    init_search_path();

    search_path path = get_lean_path_from_env().value_or(get_builtin_search_path());

    options opts;
    optional<std::string> server_in;
    std::string native_output;
    optional<std::string> c_output;
    while (true) {
        int c = getopt_long(argc, argv, g_opt_str, g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        switch (c) {
            case 'j':
                // num_threads = static_cast<unsigned>(atoi(optarg));
                break;
            case 'v':
                display_header(std::cout);
                return 0;
            case 'g':
                std::cout << LEAN_GITHASH << "\n";
                return 0;
            case 'h':
                display_help(std::cout);
                return 0;
            case 'c':
                c_output = optarg;
                break;
            case 'C':
                c_output = optarg;
                break;
            case 's':
                lean::lthread::set_thread_stack_size(
                        static_cast<size_t>((atoi(optarg) / 4) * 4) * static_cast<size_t>(1024));
                break;
            case 'i':
                use_stdin = true;
                break;
            case 'r':
                run = true;
                break;
            case 'm':
                make_mode = true;
                break;
            case 'M':
                opts = opts.update(get_max_memory_opt_name(), static_cast<unsigned>(atoi(optarg)));
                break;
            case 'T':
                opts = opts.update(get_timeout_opt_name(), static_cast<unsigned>(atoi(optarg)));
                break;
            case 't':
                trust_lvl = atoi(optarg);
                break;
            case 'q':
                opts = opts.update(lean::get_verbose_opt_name(), false);
                break;
            case 'd':
                only_deps = true;
                break;
            case 'a':
                stats = true;
                break;
            case 'D':
                try {
                    opts = set_config_option(opts, optarg);
                } catch (lean::exception & ex) {
                    std::cerr << ex.what() << std::endl;
                    return 1;
                }
                break;
#if defined(LEAN_JSON)
            case 'J':
                opts = opts.update(lean::name{"trace", "as_messages"}, true);
                json_output = true;
                break;
#endif
            case 'P':
                opts = opts.update("profiler", true);
                break;
#if defined(LEAN_DEBUG)
            case 'B':
                lean::enable_debug(optarg);
                break;
#endif
            case 'n':
                new_frontend = true;
                break;
            default:
                std::cerr << "Unknown command line option\n";
                display_help(std::cerr);
                return 1;
        }
    }

    if (auto max_memory = opts.get_unsigned(get_max_memory_opt_name(),
                                            opts.get_bool("server") ? LEAN_SERVER_DEFAULT_MAX_MEMORY
                                                                    : LEAN_DEFAULT_MAX_MEMORY)) {
        set_max_memory_megabyte(max_memory);
    }

    if (auto timeout = opts.get_unsigned(get_timeout_opt_name(),
                                         opts.get_bool("server") ? LEAN_SERVER_DEFAULT_MAX_HEARTBEAT
                                                                 : LEAN_DEFAULT_MAX_HEARTBEAT)) {
        set_max_heartbeat_thousands(timeout);
    }

    if (get_profiler(opts)) {
        report_profiling_time("initialization", init_time);
    }

    environment env(trust_lvl);

    io_state ios(opts, lean::mk_pretty_formatter_factory());

    if (json_output) ios.set_regular_channel(ios.get_diagnostic_channel_ptr());

    scope_global_ios scope_ios(ios);
    type_context_old trace_ctx(env, opts);
    scope_trace_env scope_trace(env, opts, trace_ctx);
    name main_module_name;

    std::string mod_fn = "<unknown>";
    std::string contents;
    if (use_stdin) {
        if (argc - optind != 0) {
            std::cerr << "Expected exactly one of file name or --stdin\n";
            display_help(std::cerr);
            return 1;
        }
        mod_fn = "<stdin>";
        std::stringstream buf;
        buf << std::cin.rdbuf();
        contents = buf.str();
        main_module_name = name("_stdin");
    } else {
        if (!run && argc - optind != 1) {
            std::cerr << "Expected exactly one file name\n";
            display_help(std::cerr);
            return 1;
        }
        mod_fn = lrealpath(argv[optind++]);
        contents = read_file(mod_fn);
        main_module_name = module_name_of_file2(mod_fn);
    }

    try {
        bool ok = true;
        if (new_frontend) {
            ok = lean::test_module_parser(env, contents, mod_fn);
        } else {
            scope_traces_as_messages scope_trace_msgs(mod_fn, {1, 0});
            simple_pos_info_provider pip(mod_fn.c_str());
            scope_pos_info_provider scope_pip(pip);

            // TODO(Sebastian): parse imports using new frontend
            std::vector<rel_module_name> rel_imports;
            std::istringstream in(contents);
            parser p(env, ios, in, mod_fn);
            p.parse_imports(rel_imports);

            std::vector<module_name> imports;
            auto dir = dirname(mod_fn);
            for (auto const & rel : rel_imports)
                imports.push_back(absolutize_module_name(path, dir, rel));

            if (only_deps) {
                for (auto const & import : imports) {
                    std::string m_name = find_lean_file(import);
                    auto last_idx = m_name.find_last_of(".");
                    std::string rawname = m_name.substr(0, last_idx);
                    std::string ext = m_name.substr(last_idx);
                    m_name = rawname + ".olean";
                    std::cout << m_name << "\n";
                }
                return 0;
            }

            message_log l;
            scope_message_log scope_log(l);
            if (stats) {
                timeit timer(std::cout, "import");
                env = import_modules(trust_lvl, imports);
            } else {
                env = import_modules(trust_lvl, imports);
            }
            env.set_main_module(main_module_name);
            p.set_env(env);
            p.parse_commands();

            if (json_output) {
#if defined(LEAN_JSON)
                for (auto const & msg : l.to_buffer()) {
                    print_json(std::cout, msg);
#endif
                }
            } else {
                // Messages have already been printed directly to stdout
            }
            ok = !l.has_errors();
            env = p.env();
        }

        if (stats) {
            env.display_stats();
        }

        if (run && ok) {
            return ir::run_main(env, argc - optind, argv + optind);
        }
        if (make_mode && ok) {
            auto olean_fn = olean_of_lean(mod_fn);
            time_task t(".olean serialization",
                        message_builder(environment(), get_global_ios(), mod_fn, pos_info(),
                                        message_severity::INFORMATION));
            write_module(env, olean_fn);
        }

        if (!json_output)
            display_cumulative_profiling_times(std::cerr);

        if (c_output && ok) {
            std::ofstream out(*c_output);
            if (out.fail()) {
                std::cerr << "failed to create '" << *c_output << "'\n";
                return 1;
            }
            auto mod = module_name_of_file2(mod_fn);
            out << lean::ir::emit_c(env, mod).data();
            out.close();
        }

        return ok ? 0 : 1;
    } catch (lean::throwable & ex) {
        std::cerr << lean::message_builder(env, ios, mod_fn, lean::pos_info(1, 1), lean::ERROR).set_exception(
                ex).build();
    } catch (std::bad_alloc & ex) {
        std::cerr << "out of memory" << std::endl;
    }
    return 1;
}
