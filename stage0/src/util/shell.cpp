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
#include "runtime/load_dynlib.h"
#include "runtime/array_ref.h"
#include "runtime/object_ref.h"
#include "util/timer.h"
#include "util/macros.h"
#include "util/io.h"
#include "util/options.h"
#include "util/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "library/formatter.h"
#include "library/module.h"
#include "library/time_task.h"
#include "library/compiler/ir.h"
#include "library/trace.h"
#include "library/print.h"
#include "initialize/init.h"
#include "library/compiler/ir_interpreter.h"
#include "util/path.h"
#include "stdlib_flags.h"
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

#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <dlfcn.h>
#endif

#ifdef _MSC_VER
// extremely simple implementation of getopt.h
enum arg_opt { no_argument, required_argument, optional_argument };

struct option {
    const char name[20];
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

extern "C" void *initialize_Lean_Compiler_IR_EmitLLVM(uint8_t builtin,
                                                      lean_object *);
extern "C" object *lean_ir_emit_llvm(object *env, object *mod_name,
                                     object *filepath, object *w);

static void display_header(std::ostream & out) {
    out << "Lean (version " << get_version_string() << ", " << LEAN_STR(LEAN_BUILD_TYPE) << ")\n";
}

static void display_features(std::ostream & out) {
    out << "[";
#if defined(LEAN_LLVM)
    out << "LLVM";
#endif
    out << "]\n";
}

static void display_help(std::ostream & out) {
    display_header(out);
    std::cout << "Miscellaneous:\n";
    std::cout << "  --help -h          display this message\n";
    std::cout << "  --features -f      display features compiler provides (eg. LLVM support)\n";
    std::cout << "  --version -v       display version number\n";
    std::cout << "  --githash          display the git commit hash number used to build this binary\n";
    std::cout << "  --run              call the 'main' definition in a file with the remaining arguments\n";
    std::cout << "  --o=oname -o       create olean file\n";
    std::cout << "  --i=iname -i       create ilean file\n";
    std::cout << "  --c=fname -c       name of the C output file\n";
    std::cout << "  --bc=fname -b      name of the LLVM bitcode file\n";
    std::cout << "  --stdin            take input from stdin\n";
    std::cout << "  --root=dir         set package root directory from which the module name of the input file is calculated\n"
              << "                     (default: current working directory)\n";
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
    std::cout << "  --server           start lean in server mode\n";
    std::cout << "  --worker           start lean in server-worker mode\n";
#endif
    std::cout << "  --plugin=file      load and initialize Lean shared library for registering linters etc.\n";
    std::cout << "  --load-dynlib=file load shared library to make its symbols available to the interpreter\n";
    std::cout << "  --deps             just print dependencies of a Lean input\n";
    std::cout << "  --print-prefix     print the installation prefix for Lean and exit\n";
    std::cout << "  --print-libdir     print the installation directory for Lean's built-in libraries and exit\n";
    std::cout << "  --profile          display elaboration/type checking time for each definition/theorem\n";
    std::cout << "  --stats            display environment statistics\n";
    DEBUG_CODE(
    std::cout << "  --debug=tag        enable assertions with the given tag\n";
        )
    std::cout << "  -D name=value      set a configuration option (see set_option command)\n";
}

static int print_prefix = 0;
static int print_libdir = 0;

static struct option g_long_options[] = {
    {"version",      no_argument,       0, 'v'},
    {"help",         no_argument,       0, 'h'},
    {"githash",      no_argument,       0, 'g'},
    {"run",          no_argument,       0, 'r'},
    {"o",            optional_argument, 0, 'o'},
    {"i",            optional_argument, 0, 'i'},
    {"stdin",        no_argument,       0, 'I'},
    {"root",         required_argument, 0, 'R'},
    {"memory",       required_argument, 0, 'M'},
    {"trust",        required_argument, 0, 't'},
    {"profile",      no_argument,       0, 'P'},
    {"stats",        no_argument,       0, 'a'},
    {"quiet",        no_argument,       0, 'q'},
    {"deps",         no_argument,       0, 'd'},
    {"deps-json",    no_argument,       0, 'J'},
    {"timeout",      optional_argument, 0, 'T'},
    {"c",            optional_argument, 0, 'c'},
    {"bc",           optional_argument, 0, 'b'},
    {"features",     optional_argument, 0, 'f'},
    {"exitOnPanic",  no_argument,       0, 'e'},
#if defined(LEAN_MULTI_THREAD)
    {"threads",      required_argument, 0, 'j'},
    {"tstack",       required_argument, 0, 's'},
    {"server",       no_argument,       0, 'S'},
    {"worker",       no_argument,       0, 'W'},
#endif
    {"plugin",       required_argument, 0, 'p'},
    {"load-dynlib",  required_argument, 0, 'l'},
    {"print-prefix", no_argument,       &print_prefix, 1},
    {"print-libdir", no_argument,       &print_libdir, 1},
#ifdef LEAN_DEBUG
    {"debug",        required_argument, 0, 'B'},
#endif
    {0, 0, 0, 0}
};

static char const * g_opt_str =
    "PdD:o:i:b:c:C:qgvht:012j:012rR:M:012T:012ap:e"
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

void load_plugin(std::string path) {
    void * init;
    // we never want to look up plugins using the system library search
    path = lrealpath(path);
    std::string pkg = stem(path);
    std::string sym = "initialize_" + pkg;
#ifdef LEAN_WINDOWS
    HMODULE h = LoadLibrary(path.c_str());
    if (!h) {
        throw exception(sstream() << "error loading plugin " << path << ": " << GetLastError());
    }
    init = reinterpret_cast<void *>(GetProcAddress(h, sym.c_str()));
#else
    void *handle = dlopen(path.c_str(), RTLD_LAZY);
    if (!handle) {
        throw exception(sstream() << "error loading plugin, " << dlerror());
    }
    init = dlsym(handle, sym.c_str());
#endif
    if (!init) {
        throw exception(sstream() << "error, plugin " << path << " does not seem to contain a module '" << pkg << "'");
    }
    auto init_fn = reinterpret_cast<object *(*)(uint8_t, object *)>(init);
    object *r = init_fn(1 /* builtin */, io_mk_world());
    consume_io_result(r);
    // NOTE: we never unload plugins
}

namespace lean {
extern "C" object * lean_run_frontend(
    object * input,
    object * opts,
    object * filename,
    object * main_module_name,
    uint32_t trust_level,
    object * ilean_filename,
    object * w
);
pair_ref<environment, object_ref> run_new_frontend(
    std::string const & input,
    options const & opts, std::string const & file_name,
    name const & main_module_name,
    uint32_t trust_level,
    optional<std::string> const & ilean_file_name
) {
    object * oilean_file_name = mk_option_none();
    if (ilean_file_name) {
        oilean_file_name = mk_option_some(mk_string(*ilean_file_name));
    }
    return get_io_result<pair_ref<environment, object_ref>>(lean_run_frontend(
        mk_string(input),
        opts.to_obj_arg(),
        mk_string(file_name),
        main_module_name.to_obj_arg(),
        trust_level,
        oilean_file_name,
        io_mk_world()
    ));
}

/* def workerMain : Options → IO UInt32 */
extern "C" object * lean_server_worker_main(object * opts, object * w);
uint32_t run_server_worker(options const & opts) {
    return get_io_scalar_result<uint32_t>(lean_server_worker_main(opts.to_obj_arg(), io_mk_world()));
}

/* def watchdogMain (args : List String) : IO Uint32 */
extern "C" object* lean_server_watchdog_main(object* args, object* w);
uint32_t run_server_watchdog(buffer<string_ref> const & args) {
    list_ref<string_ref> arglist = to_list_ref(args);
    return get_io_scalar_result<uint32_t>(lean_server_watchdog_main(arglist.to_obj_arg(), io_mk_world()));
}

extern "C" object* lean_init_search_path(object* w);
void init_search_path() {
    get_io_scalar_result<unsigned>(lean_init_search_path(io_mk_world()));
}

extern "C" object* lean_module_name_of_file(object* fname, object * root_dir, object* w);
optional<name> module_name_of_file(std::string const & fname, optional<std::string> const & root_dir, bool optional) {
    object * oroot_dir = mk_option_none();
    if (root_dir) {
        oroot_dir = mk_option_some(mk_string(*root_dir));
    }
    object * o = lean_module_name_of_file(mk_string(fname), oroot_dir, io_mk_world());
    if (io_result_is_error(o) && optional) {
        return lean::optional<name>();
    } else {
        return some(get_io_result<name>(o));
    }
}

/* def printImports (input : String) (fileName : Option String := none) : IO Unit */
extern "C" object* lean_print_imports(object* input, object* file_name, object* w);
void print_imports(std::string const & input, std::string const & fname) {
    consume_io_result(lean_print_imports(mk_string(input), mk_option_some(mk_string(fname)), io_mk_world()));
}

/* def printImportsJson (fileNames : Array String) : IO Unit */
extern "C" object* lean_print_imports_json(object * file_names, object * w);
void print_imports_json(array_ref<string_ref> const & fnames) {
    consume_io_result(lean_print_imports_json(fnames.to_obj_arg(), io_mk_world()));
}

extern "C" object* lean_environment_free_regions(object * env, object * w);
void environment_free_regions(environment && env) {
    consume_io_result(lean_environment_free_regions(env.steal(), io_mk_world()));
}
}

extern "C" object * lean_get_prefix(object * w);
extern "C" object * lean_get_libdir(object * sysroot, object * w);

void check_optarg(char const * option_name) {
    if (!optarg) {
        std::cerr << "error: argument missing for option '-" << option_name << "'" << std::endl;
        std::exit(1);
    }
}

extern "C" object * lean_enable_initializer_execution(object * w);

extern "C" LEAN_EXPORT int lean_main(int argc, char ** argv) {
#ifdef LEAN_EMSCRIPTEN
    // When running in command-line mode under Node.js, we make system directories available in the virtual filesystem.
    // This mode is used to compile 32-bit oleans.
    EM_ASM(
        if ((typeof process === "undefined") || (process.release.name !== "node")) {
            throw new Error("The Lean command-line driver can only run under Node.js. For the embeddable WASM library, see lean_wasm.cpp.");
        }

        var lean_path = process.env["LEAN_PATH"];
        if (lean_path) {
            ENV["LEAN_PATH"] = lean_path;
        }

        // We cannot mount /, see https://github.com/emscripten-core/emscripten/issues/2040
        FS.mount(NODEFS, { root: "/home" }, "/home");
        FS.mount(NODEFS, { root: "/tmp" }, "/tmp");
        FS.chdir(process.cwd());
    );
#elif defined(LEAN_WINDOWS)
    // "best practice" according to https://docs.microsoft.com/en-us/windows/win32/api/errhandlingapi/nf-errhandlingapi-seterrormode
    SetErrorMode(SEM_FAILCRITICALERRORS);
#endif
    auto init_start = std::chrono::steady_clock::now();
    lean::initializer init;
    second_duration init_time = std::chrono::steady_clock::now() - init_start;
    bool run = false;
    optional<std::string> olean_fn;
    optional<std::string> ilean_fn;
    bool use_stdin = false;
    unsigned trust_lvl = LEAN_BELIEVER_TRUST_LEVEL + 1;
    bool only_deps = false;
    bool deps_json = false;
    bool stats = false;
    // 0 = don't run server, 1 = watchdog, 2 = worker
    int run_server = 0;
    unsigned num_threads    = 0;
#if defined(LEAN_MULTI_THREAD)
    num_threads = hardware_concurrency();
#endif

    try {
        // Remark: This currently runs under `IO.initializing = true`.
        init_search_path();
    } catch (lean::throwable & ex) {
        std::cerr << "error: " << ex.what() << std::endl;
        return 1;
    }
    consume_io_result(lean_enable_initializer_execution(io_mk_world()));

    options opts = get_default_options();
    optional<std::string> server_in;
    std::string native_output;
    optional<std::string> c_output;
    optional<std::string> llvm_output;
    optional<std::string> root_dir;
    buffer<string_ref> forwarded_args;

    while (true) {
        int c = getopt_long(argc, argv, g_opt_str, g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        if (c == 0)
            continue; // long-only option
        switch (c) {
            case 'e':
                lean_set_exit_on_panic(true);
                break;
            case 'j':
                num_threads = static_cast<unsigned>(atoi(optarg));
                forwarded_args.push_back(string_ref("-j" + std::string(optarg)));
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
            case 'f':
                display_features(std::cout);
                return 0;
            case 'c':
                check_optarg("c");
                c_output = optarg;
                break;
            case 'b':
                check_optarg("bc");
                llvm_output = optarg;
                break;
            case 's':
                lean::lthread::set_thread_stack_size(
                        static_cast<size_t>((atoi(optarg) / 4) * 4) * static_cast<size_t>(1024));
                forwarded_args.push_back(string_ref("-s" + std::string(optarg)));
                break;
            case 'I':
                use_stdin = true;
                break;
            case 'r':
                run = true;
                break;
            case 'o':
                olean_fn = optarg;
                break;
            case 'i':
                ilean_fn = optarg;
                break;
            case 'R':
                root_dir = optarg;
                forwarded_args.push_back(string_ref("-R" + std::string(optarg)));
                break;
            case 'M':
                check_optarg("M");
                opts = opts.update(get_max_memory_opt_name(), static_cast<unsigned>(atoi(optarg)));
                forwarded_args.push_back(string_ref("-M" + std::string(optarg)));
                break;
            case 'T':
                check_optarg("T");
                opts = opts.update(get_timeout_opt_name(), static_cast<unsigned>(atoi(optarg)));
                forwarded_args.push_back(string_ref("-T" + std::string(optarg)));
                break;
            case 't':
                check_optarg("t");
                trust_lvl = atoi(optarg);
                forwarded_args.push_back(string_ref("-t" + std::string(optarg)));
                break;
            case 'q':
                opts = opts.update(lean::get_verbose_opt_name(), false);
                break;
            case 'd':
                only_deps = true;
                break;
            case 'J':
                only_deps = true;
                deps_json = true;
                break;
            case 'a':
                stats = true;
                break;
            case 'D':
                try {
                    check_optarg("D");
                    opts = set_config_option(opts, optarg);
                    forwarded_args.push_back(string_ref("-D" + std::string(optarg)));
                } catch (lean::exception & ex) {
                    std::cerr << ex.what() << std::endl;
                    return 1;
                }
                break;
            case 'S':
                run_server = 1;
                break;
            case 'W':
                run_server = 2;
                break;
            case 'P':
                opts = opts.update("profiler", true);
                break;
#if defined(LEAN_DEBUG)
            case 'B':
                check_optarg("B");
                lean::enable_debug(optarg);
                break;
#endif
            case 'p':
                check_optarg("p");
                load_plugin(optarg);
                forwarded_args.push_back(string_ref("--plugin=" + std::string(optarg)));
                break;
            case 'l':
                check_optarg("l");
                lean::load_dynlib(optarg);
                forwarded_args.push_back(string_ref("--load-dynlib=" + std::string(optarg)));
                break;
            default:
                std::cerr << "Unknown command line option\n";
                display_help(std::cerr);
                return 1;
        }
    }

    lean::io_mark_end_initialization();

    if (print_prefix) {
        std::cout << get_io_result<string_ref>(lean_get_prefix(io_mk_world())).data() << std::endl;
        return 0;
    }

    if (print_libdir) {
        string_ref prefix = get_io_result<string_ref>(lean_get_prefix(io_mk_world()));
        std::cout << get_io_result<string_ref>(lean_get_libdir(prefix.to_obj_arg(), io_mk_world())).data() << std::endl;
        return 0;
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
    scoped_task_manager scope_task_man(num_threads);
    optional<name> main_module_name;

    std::string mod_fn = "<unknown>";
    std::string contents;

    try {
        if (run_server == 1)
            return run_server_watchdog(forwarded_args);
        else if (run_server == 2)
            return run_server_worker(opts);

        if (only_deps && deps_json) {
            buffer<string_ref> fns;
            if (use_stdin) {
                std::string fn;
                while (std::cin >> fn) {
                    fns.push_back(string_ref(fn));
                }
            } else {
                for (int i = optind; i < argc; i++) {
                    fns.push_back(string_ref(argv[i]));
                }
            }
            print_imports_json(fns);
            return 0;
        }

        if (use_stdin) {
            if (argc - optind != 0) {
                mod_fn = argv[optind++];
            } else {
                mod_fn = "<stdin>";
            }
            std::stringstream buf;
            buf << std::cin.rdbuf();
            contents = buf.str();
        } else {
            if ((!run && argc - optind != 1) || (run && argc - optind == 0)) {
                std::cerr << "Expected exactly one file name\n";
                display_help(std::cerr);
                return 1;
            }
            mod_fn = argv[optind++];
            contents = read_file(mod_fn);
            main_module_name = module_name_of_file(mod_fn, root_dir, /* optional */ !olean_fn && !c_output);
        }

        if (only_deps) {
            print_imports(contents, mod_fn);
            return 0;
        }

        // Quick and dirty `#lang` support
        // TODO: make it extensible, and add `lean4md`
        if (contents.compare(0, 5, "#lang") == 0) {
            auto end_line_pos = contents.find("\n");
            // TODO: trim
            auto lang_id      = contents.substr(6, end_line_pos - 6);
            if (lang_id == "lean4") {
                // do nothing for now
            } else {
                std::cerr << "unknown language '" << lang_id << "'\n";
                return 1;
            }
            // Remove up to `\n`
            contents.erase(0, end_line_pos);
        }

        if (!main_module_name)
            main_module_name = name("_stdin");
        pair_ref<environment, object_ref> r = run_new_frontend(contents, opts, mod_fn, *main_module_name, trust_lvl, ilean_fn);
        env = r.fst();
        bool ok = unbox(r.snd().raw());

        if (stats) {
            env.display_stats();
        }

        if (run && ok) {
            uint32 ret = ir::run_main(env, opts, argc - optind, argv + optind);
            // environment_free_regions(std::move(env));
            return ret;
        }
        if (olean_fn && ok) {
            time_task t(".olean serialization", opts);
            write_module(env, *olean_fn);
        }

        if (c_output && ok) {
            std::ofstream out(*c_output, std::ios_base::binary);
            if (out.fail()) {
                std::cerr << "failed to create '" << *c_output << "'\n";
                return 1;
            }
            time_task _("C code generation", opts);
            out << lean::ir::emit_c(env, *main_module_name).data();
            out.close();
        }

        if (llvm_output && ok) {
            initialize_Lean_Compiler_IR_EmitLLVM(/*builtin*/ false,
                    lean_io_mk_world());
            time_task _("LLVM code generation", opts);
            lean::consume_io_result(lean_ir_emit_llvm(
                        env.to_obj_arg(), (*main_module_name).to_obj_arg(),
                        lean::string_ref(*llvm_output).to_obj_arg(),
                        lean_io_mk_world()));
        }

        display_cumulative_profiling_times(std::cerr);

#ifdef LEAN_SMALL_ALLOCATOR
        // If the small allocator is not enabled, then we assume we are not using the sanitizer.
        // Thus, we interrupt execution without garbage collecting.
        // This is useful when profiling improvements to Lean startup time.
        exit(ok ? 0 : 1);
#else
        return ok ? 0 : 1;
#endif
    } catch (lean::throwable & ex) {
        std::cerr << ex.what() << "\n";
    } catch (std::bad_alloc & ex) {
        std::cerr << "out of memory" << std::endl;
    }
    return 1;
}
