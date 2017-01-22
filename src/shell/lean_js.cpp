/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/module_mgr.h"
#include "library/st_task_queue.h"
#include "library/module.h"
#include "kernel/standard_kernel.h"
#include "library/type_context.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"
#include "init/init.h"
#include "shell/simple_pos_info_provider.h"
#include "shell/server.h"

namespace lean {
class emscripten_shell {
private:
    environment m_env;
    io_state m_ios;
    server m_server;

    st_task_queue m_tq;

    json_message_stream m_msg_buf;
public:
    emscripten_shell(): m_env(mk_environment(LEAN_BELIEVER_TRUST_LEVEL + 1)),
                        m_ios(options({"trace", "as_messages"}, true),
                              mk_pretty_formatter_factory()),
                        m_server(0, m_env, m_ios),
                        m_msg_buf(std::cout) { }

    int process_request(std::string msg) {
        scope_global_task_queue scope_tq(&m_tq);
        scope_global_ios scoped_ios(m_ios);
        scoped_message_buffer scope_msg_buf(&m_msg_buf);
        scope_message_context msg_ctx(message_bucket_id { "lean.js", 0 });
        try {
            m_server.handle_request(json::parse(msg));
            return 0;
        } catch (std::exception & ex) {
            message_builder(m_env, m_ios, "processing request", {1, 0}, ERROR).set_exception(ex).report();
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

int emscripten_process_request(uintptr_t msg) {
    return g_shell->process_request(reinterpret_cast<char *>(msg));
}
