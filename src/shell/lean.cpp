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
#include "library/eval_helper.h"
#include "util/timer.h"
#include "util/task_builder.h"
#include "util/stackinfo.h"
#include "util/macros.h"
#include "util/debug.h"
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/memory.h"
#include "util/thread.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker.h"
#include "kernel/formatter.h"
#include "library/st_task_queue.h"
#include "library/mt_task_queue.h"
#include "library/module_mgr.h"
#include "kernel/standard_kernel.h"
#include "library/module.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"
#include "library/export.h"
#include "library/message_builder.h"
#include "library/time_task.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/dependencies.h"
#include "frontends/lean/json.h"
#include "frontends/lean/util.h"
#include "library/trace.h"
#include "init/init.h"
#include "shell/simple_pos_info_provider.h"
#include "shell/leandoc.h"
#ifdef _MSC_VER
#include <io.h>
#define STDOUT_FILENO 1
#else
#include <getopt.h>
#include <unistd.h>
#endif
#if defined(LEAN_JSON)
#include "shell/server.h"
#endif
#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#endif
#include "githash.h" // NOLINT

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
    std::cout << "  --doc=file -r      generate module documentation based on module doc strings\n";
    std::cout << "  --make             create olean files\n";
    std::cout << "  --recursive        recursively find *.lean files in directory arguments\n";
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
    std::cout << "  --path             display the path used for finding Lean libraries and extensions\n";
    std::cout << "  --json             print JSON-formatted structured error messages\n";
    std::cout << "  --server           start lean in server mode\n";
    std::cout << "  --server=file      start lean in server mode, redirecting standard input from the specified file (for debugging)\n";
#endif
    std::cout << "  --profile          display elaboration/type checking time for each definition/theorem\n";
    DEBUG_CODE(
    std::cout << "  --debug=tag        enable assertions with the given tag\n";
        )
    std::cout << "  -D name=value      set a configuration option (see set_option command)\n";
    std::cout << "Exporting data:\n";
    std::cout << "  --export=file -E   export final environment as textual low-level file\n";
    std::cout << "  --only-export=decl_name   only export the specified declaration (+ dependencies)\n";
    std::cout << "  --test-suite       capture output and status code from each input file $f in $f.produced and $f.status, respectively\n";
}

static struct option g_long_options[] = {
    {"version",      no_argument,       0, 'v'},
    {"help",         no_argument,       0, 'h'},
    {"run",          required_argument, 0, 'a'},
    {"githash",      no_argument,       0, 'g'},
    {"make",         no_argument,       0, 'm'},
    {"recursive",    no_argument,       0, 'R'},
    {"export",       required_argument, 0, 'E'},
    {"only-export",  required_argument, 0, 'o'},
    {"memory",       required_argument, 0, 'M'},
    {"trust",        required_argument, 0, 't'},
    {"profile",      no_argument,       0, 'P'},
    {"threads",      required_argument, 0, 'j'},
    {"quiet",        no_argument,       0, 'q'},
    {"deps",         no_argument,       0, 'd'},
    {"test-suite",   no_argument,       0, 'e'},
    {"timeout",      optional_argument, 0, 'T'},
#if defined(LEAN_JSON)
    {"json",         no_argument,       0, 'J'},
    {"path",         no_argument,       0, 'p'},
    {"server",       optional_argument, 0, 'S'},
#endif
    {"doc",          required_argument, 0, 'r'},
#if defined(LEAN_MULTI_THREAD)
    {"tstack",       required_argument, 0, 's'},
#endif
#ifdef LEAN_DEBUG
    {"debug",        required_argument, 0, 'B'},
#endif
    {0, 0, 0, 0}
};

static char const * g_opt_str =
    "PdD:qpgvhet:012E:A:B:j:012rM:012T:012"
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
        case lean::BoolOption:
            if (val == "true")
                return opts.update(opt, true);
            else if (val == "false")
                return opts.update(opt, false);
            else
                throw lean::exception(lean::sstream() << "invalid -D parameter, invalid configuration option '" << opt
                                      << "' value, it must be true/false");
        case DoubleOption:
            return opts.update(opt, atof(val.c_str()));
        case lean::IntOption:
        case lean::UnsignedOption:
            return opts.update(opt, atoi(val.c_str()));
        case lean::StringOption:
            return opts.update(opt, val);
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
#if defined(LEAN_JSON)
        lean::initialize_server();
#endif
    }
    ~initializer() {
#if defined(LEAN_JSON)
        lean::finalize_server();
#endif
    }
};

class progress_message_stream {
    mutex m_mutex;
    bool m_showing_task = false;
    std::ostream & m_out;
    bool m_use_json;
    log_tree::node m_lt;

    bool m_show_progress;
    std::unique_ptr<single_timer> m_timer;
    std::string m_last_task;

    void clear_shown_task() {
        if (m_showing_task) {
            m_out << "\33[2K\r";
            m_showing_task = false;
        }
    }

public:
    progress_message_stream(std::ostream & out, bool use_json, bool show_progress, log_tree::node const & lt) :
            m_out(out), m_use_json(use_json), m_lt(lt), m_show_progress(show_progress) {
#if defined(LEAN_MULTI_THREAD)
        if (show_progress) {
            m_timer.reset(new single_timer);
        }
#endif
    }

    ~progress_message_stream() {
        m_timer.reset();
        clear_shown_task();
    }

    void on_event(std::vector<log_tree::event> const & events) {
        bool refresh_task = false;
        for (auto & e : events) {
            switch (e.m_kind) {
                case log_tree::event::EntryAdded:
                    if (auto msg = dynamic_cast<message const *>(e.m_entry.get())) {
                        unique_lock<mutex> lock(m_mutex);
                        clear_shown_task();
                        if (m_use_json) {
#if defined(LEAN_JSON)
                            print_json(m_out, *msg);
#endif
                        } else {
                            m_out << *msg;
                        }
                    }
                    break;
                case log_tree::event::EntryRemoved: break;
                case log_tree::event::ProducerSet:
                    taskq().submit(e.m_node.get_producer());
                    break;
                case log_tree::event::StateChanged:
                    refresh_task = true;
                    break;
            }
        }
        if (m_show_progress && refresh_task) {
#if defined(LEAN_MULTI_THREAD)
            lean_assert(m_timer);
            m_timer->set(chrono::steady_clock::now() + chrono::milliseconds(100),
                [=] { show_current_task(); }, false);
#else
            show_current_task_core();
#endif
        }
    }

    optional<std::string> find_current_task() {
        optional<std::string> found_running;
        m_lt.for_each([&] (log_tree::node const & lt) {
            if (!found_running) {
                if (lt.get_state() == log_tree::state::Running) {
                    std::ostringstream fmt;
                    fmt << lt.get_location().m_file_name << ": " << lt.get_description();
                    found_running = fmt.str();
                }
            }
            return !found_running;
        });
        return found_running;
    }

    void show_current_task() {
        unique_lock<mutex> lock(m_mutex);
        show_current_task_core();
    }
    void show_current_task_core() {
        if (m_use_json) return;
        if (auto desc = find_current_task()) {
            if (*desc == m_last_task && m_showing_task) return;
            m_last_task = *desc;
            clear_shown_task();
#if defined(LEAN_EMSCRIPTEN)
            m_out << *desc << std::endl;
#else
            m_out << *desc << std::flush;
            m_showing_task = true;
#endif
        }
    }
};

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
    ::initializer init;
    bool make_mode          = false;
    bool recursive          = false;
    unsigned trust_lvl      = LEAN_BELIEVER_TRUST_LEVEL+1;
    bool only_deps          = false;
    bool test_suite         = false;
    unsigned num_threads    = 0;
#if defined(LEAN_MULTI_THREAD)
    num_threads = hardware_concurrency();
#endif
#if defined(LEAN_JSON)
    bool json_output        = false;
#endif

    standard_search_path path;

    options opts;
    optional<std::string> export_txt;
    buffer<name> only_export;
    optional<std::string> doc;
    optional<std::string> server_in;
    optional<std::string> run_arg;
    std::string native_output;
    while (true) {
        int c = getopt_long(argc, argv, g_opt_str, g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        switch (c) {
        case 'j':
            num_threads = static_cast<unsigned>(atoi(optarg));
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
        case 'a':
            run_arg = optarg;
            break;
        case 's':
            lean::lthread::set_thread_stack_size(static_cast<size_t>((atoi(optarg)/4)*4)*static_cast<size_t>(1024));
            break;
        case 'm':
            make_mode = true;
            recursive = true;
            break;
        case 'R':
            recursive = true;
            break;
        case 'n':
            native_output         = optarg;
            break;
        case 'r':
            doc = optarg;
            break;
        case 'M':
            opts = opts.update(get_max_memory_opt_name(), atoi(optarg));
            break;
        case 'T':
            opts = opts.update(get_timeout_opt_name(), atoi(optarg));
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
        case 'S':
            opts = opts.update("server", true);
            opts = opts.update(lean::name{"trace", "as_messages"}, true);
            if (optarg) server_in = optional<std::string>(optarg);
            break;
        case 'p': {
            json out;

            auto & out_path = out["path"] = json::array();
            for (auto & p : path.get_path()) out_path.push_back(p);

            out["leanpkg_path_file"] = path.m_leanpkg_path_fn ? *path.m_leanpkg_path_fn : path.m_user_leanpkg_path_fn;
            out["is_user_leanpkg_path"] = !path.m_leanpkg_path_fn;

            std::cout << std::setw(2) << out << std::endl;
            return 0;
        }
#endif
        case 'P':
            opts = opts.update("profiler", true);
            break;
        case 'E':
            export_txt = std::string(optarg);
            break;
        case 'o':
            only_export.push_back(string_to_name(optarg));
            break;
        case 'e':
            test_suite = true;
            opts = opts.update(lean::name{"trace", "as_messages"}, true);
            break;
#if defined(LEAN_DEBUG)
        case 'B':
            lean::enable_debug(optarg);
            break;
#endif
        default:
            std::cerr << "Unknown command line option\n";
            display_help(std::cerr);
            return 1;
        }
        if (run_arg) {
            // treat run_arg as the last arg
            break;
        }
    }

    if (auto max_memory = opts.get_unsigned(get_max_memory_opt_name(),
                                            opts.get_bool("server") ? LEAN_SERVER_DEFAULT_MAX_MEMORY : LEAN_DEFAULT_MAX_MEMORY)) {
        set_max_memory_megabyte(max_memory);
    }

    if (auto timeout = opts.get_unsigned(get_timeout_opt_name(),
                                         opts.get_bool("server") ? LEAN_SERVER_DEFAULT_MAX_HEARTBEAT : LEAN_DEFAULT_MAX_HEARTBEAT)) {
        set_max_heartbeat_thousands(timeout);
    }

    environment env = mk_environment(trust_lvl);

    io_state ios(opts, lean::mk_pretty_formatter_factory());

#if defined(LEAN_JSON)
    if (opts.get_bool("server")) {
        /* Disable assertion violation dialog:
           (C)ontinue, (A)bort, (S)top, Invoke (G)DB */
        lean::enable_debug_dialog(false);

        std::unique_ptr<std::ifstream> file_in;
        if (server_in) {
            file_in.reset(new std::ifstream(*server_in));
            if (!file_in->is_open()) {
                std::cerr << "cannot open file " << *server_in << std::endl;
                return 1;
            }
            std::cin.rdbuf(file_in->rdbuf());
        }

        server(num_threads, path.get_path(), env, ios).run();
        return 0;
    }
#endif

    log_tree lt;

    bool show_progress = make_mode && isatty(STDOUT_FILENO);
    progress_message_stream msg_stream(std::cout, json_output, show_progress, lt.get_root());
    if (json_output) ios.set_regular_channel(ios.get_diagnostic_channel_ptr());

    if (!test_suite)
        lt.add_listener([&] (std::vector<log_tree::event> const & evs) { msg_stream.on_event(evs); });
    auto lt_root = lt.get_root();
    scope_log_tree_core scope_lt(&lt_root);

    scope_global_ios scope_ios(ios);

    try {
        std::shared_ptr<task_queue> tq;
#if defined(LEAN_MULTI_THREAD)
        if (num_threads == 0) {
            tq = std::make_shared<st_task_queue>();
        } else {
            tq = std::make_shared<mt_task_queue>(num_threads);
        }
#else
        tq = std::make_shared<st_task_queue>();
#endif
        set_task_queue(tq.get());

        fs_module_vfs vfs;
        module_mgr mod_mgr(&vfs, lt.get_root(), path.get_path(), env, ios);

        if (run_arg) {
            auto mod = mod_mgr.get_module(lrealpath(*run_arg));
            if (!mod) throw exception(sstream() << "could not load " << *run_arg);

            auto main_env = get(get(mod->m_result).m_loaded_module->m_env);
            auto main_opts = get(mod->m_result).m_opts;
            set_io_cmdline_args({argv + optind, argv + argc});
            eval_helper fn(main_env, main_opts, "main");

            type_context_old tc(main_env, main_opts);
            scope_trace_env scope2(main_env, main_opts, tc);

            try {
                if (fn.try_exec()) {
                    return 0;
                } else {
                    throw exception(sstream() << *run_arg << ": cannot execute main function with type "
                                              << ios.get_formatter_factory()(main_env, main_opts, tc)(fn.get_type()));
                }
            } catch (std::exception & ex) {
                std::cerr << ex.what() << std::endl;
                return 1;
            }
        }

        mod_mgr.set_save_olean(make_mode);

        std::vector<std::string> args(argv + optind, argv + argc);
        if (recursive) {
            if (args.empty()) args.push_back(".");
            std::vector<std::string> files;
            for (auto & f : args) {
                if (auto i_d = is_dir(f)) {
                    if (*i_d) {
                        find_files(f, ".lean", files);
                    } else {
                        files.push_back(f);
                    }
                }
            }
            args.clear();
            for (auto & f : files) {
                if (is_lean_file(f))
                    args.push_back(f);
            }
        }
        std::vector<std::string> module_args;
        for (auto & f : args) module_args.push_back(lrealpath(f));

        if (!recursive) {
            for (auto & mod_id : module_args)
                vfs.m_modules_to_load_from_source.insert(mod_id);
        }

        bool ok = true;

        if (only_deps) {
            for (auto & mod_fn : module_args) {
                try {
                    if (!display_deps(path.get_path(), env, std::cout, std::cerr, mod_fn.c_str()))
                        ok = false;
                } catch (lean::exception &ex) {
                    ok = false;
                    lean::message_builder(env, ios, mod_fn, lean::pos_info(1, 1), lean::ERROR).set_exception(
                            ex).report();
                }
            }

            return ok ? 0 : 1;
        }

        struct input_mod {
            module_id m_id;
            std::shared_ptr<module_info const> m_mod_info;
        };
        std::vector<input_mod> mods;
        for (auto & mod : module_args) {
            auto mod_info = mod_mgr.get_module(mod);
            mods.push_back({mod, mod_info});
        }

        taskq().wait_for_finish(lt.get_root().wait_for_finish());

        for (auto & mod : mods) {
            if (test_suite) {
                std::ofstream out(mod.m_id + ".test_suite.out");
                mod.m_mod_info->m_lt.for_each([&](log_tree::node const & n) {
                    for (auto const & e : n.get_entries()) {
                        if (auto msg = dynamic_cast<message const *>(e.get())) {
                            out << *msg;
                        }
                    }
                    return true;
                });
            }
            bool mod_ok = true;
            try {
                auto res = get(mod.m_mod_info->m_result);
            } catch (...) {
                ok = mod_ok = false;
                // exception has already been reported
            }
            if (test_suite) {
                std::ofstream status(mod.m_id + ".status");
                status << (mod_ok && !get(has_errors(mod.m_mod_info->m_lt)) ? 0 : 1);
            }
        }

        display_cumulative_profiling_times(std::cerr);

        // if (!mods.empty() && export_native_objects) {
        //     // this code is now broken
        //     env = lean::set_native_module_path(env, lean::name(native_output));
        // }

        if (export_txt && !mods.empty()) {
            buffer<std::shared_ptr<module_info const>> mod_infos;
            for (auto & mod : mods) mod_infos.push_back(mod.m_mod_info);
            auto combined_env = get_combined_environment(mod_mgr.get_initial_env(), mod_infos);

            exclusive_file_lock export_lock(*export_txt);
            std::ofstream out(*export_txt);
            optional<list<name>> decls;
            if (!only_export.empty()) {
                decls = to_list(only_export);
            }
            export_as_lowtext(out, combined_env, decls);
        }

        if (doc) {
            exclusive_file_lock export_lock(*doc);
            std::ofstream out(*doc);
            gen_doc(env, opts, out);
        }

        return ((ok && !get(has_errors(lt.get_root()))) || test_suite) ? 0 : 1;
    } catch (lean::throwable & ex) {
        lean::message_builder(env, ios, "<unknown>", lean::pos_info(1, 1), lean::ERROR).set_exception(ex).report();
    } catch (std::bad_alloc & ex) {
        std::cerr << "out of memory" << std::endl;
    }
    return 1;
}
