/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/flycheck.h"
#include "library/module.h"
#include "library/standard_kernel.h"
#include "library/type_context.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"
#include "init/init.h"
#include "shell/simple_pos_info_provider.h"

namespace lean {
class emscripten_shell {
private:
    unsigned trust_lvl;
    unsigned num_threads;
    options opts;
    environment env;
    io_state ios;

public:
    emscripten_shell() : trust_lvl(LEAN_BELIEVER_TRUST_LEVEL+1), num_threads(1),
        env(mk_environment(trust_lvl)), ios(opts, lean::mk_pretty_formatter_factory()) {
        ios.set_message_channel(std::make_shared<flycheck_message_stream>(std::cout));
    }

    int import_module(std::string mname) {
        try {
            module_name mod(mname);
            std::string base = ".";
            bool num_threads = 1;
            // FIXME(gabriel): discarding proofs fails at the moment with "invalid equation lemma, unexpected form"
            bool keep_proofs = true;
            env = import_modules(env, base, 1, &mod, num_threads, keep_proofs, ios);
        } catch (lean::exception & ex) {
            lean::message_builder(env, ios, "import_module", lean::pos_info(1, 1), lean::ERROR).set_exception(ex).report();
            return 1;
        }
        return 0;
    }

    int process_file(std::string input_filename) {
        bool ok = true;
        try {
            environment temp_env(env);
            io_state    temp_ios(ios);
            if (!parse_commands(temp_env, temp_ios, input_filename.c_str(), optional<std::string>(), false, num_threads)) {
                ok = false;
            }
        } catch (lean::exception & ex) {
            lean::message_builder(env, ios, input_filename, lean::pos_info(1, 1), lean::ERROR).set_exception(ex).report();
            ok = false;
        }
        return ok ? 0 : 1;
    }
};
}

static lean::initializer * g_init = nullptr;
static lean::emscripten_shell * g_shell = nullptr;

void initialize_emscripten() {
    g_init  = new lean::initializer();
    g_shell = new lean::emscripten_shell();
}

void finalize_emscripten() {
    delete g_shell;
    delete g_init;
}

int emscripten_import_module(std::string mname) {
    return g_shell->import_module(mname);
}

int emscripten_process_file(std::string input_filename) {
    return g_shell->process_file(input_filename);
}
