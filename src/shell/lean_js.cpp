/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/module_mgr.h"
#include "library/st_task_queue.h"
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
    options opts;
    environment env;
    io_state ios;

    st_task_queue tq;
    scope_global_task_queue scope_tq;

    flycheck_message_stream msg_buf;
    scoped_message_buffer scope_msg_buf;

    module_mgr mod_mgr;
    scoped_task_context scope_task_ctx;

    scope_message_context msg_ctx;

public:
    emscripten_shell() : trust_lvl(LEAN_BELIEVER_TRUST_LEVEL+1),
        env(mk_environment(trust_lvl)), ios(opts, mk_pretty_formatter_factory()),
        tq(), scope_tq(&tq), msg_buf(std::cout), scope_msg_buf(&msg_buf),
        mod_mgr(nullptr, &msg_buf, env, ios), scope_task_ctx("lean.js", {1, 0}),
        msg_ctx(message_bucket_id { "lean.js", 0 }) {
    }

    int import_module(std::string mname) {
        try {
            // FIXME(gabriel): discarding proofs fails at the moment with "invalid equation lemma, unexpected form"
            env = lean::import_modules(env, "importing", {{mname, optional<unsigned>()}}, mk_olean_loader());
            return 0;
        } catch (exception & ex) {
            message_builder(env, ios, "importing", {1, 0}, ERROR).set_exception(ex).report();
            return 1;
        }
    }

    int process_file(std::string input_filename) {
        try {
            std::ifstream in(input_filename);
            bool use_exceptions = false;
            parser p(env, ios, mk_olean_loader(), in, input_filename, use_exceptions);
            if (p()) return 0;
        } catch (exception & ex) {
            message_builder(env, ios, input_filename, {1, 0}, ERROR).set_exception(ex).report();
        }
        return 1;
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
