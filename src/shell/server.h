/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Sebastian Ullrich
*/
#pragma once
#include <string>
#include "kernel/pos_info_provider.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/versioned_msg_buf.h"
#include "library/module_mgr.h"
#include "frontends/lean/json.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)
mt_tq_prioritizer mk_interactive_prioritizer(module_id const & roi);
#endif

class server : public module_vfs {
    versioned_msg_buf m_msg_buf;
    task_queue * m_tq;
    module_mgr * m_mod_mgr;
    fs_module_vfs m_fs_vfs;

    options m_opts;
    environment m_initial_env;
    io_state m_ios;

    struct editor_file {
        time_t m_mtime;
        std::string m_content;
    };
    std::unordered_map<std::string, editor_file> m_open_files;

    std::string m_visible_file;

    std::shared_ptr<snapshot const> get_closest_snapshot(module_id const & id, unsigned linenum);

    json handle_request(json const & req);

    json handle_sync(json const & req);
    json handle_check(json const & req);
    json handle_complete(json const & req);
    json handle_info(json const & req);

    json serialize_decl(name const & short_name, name const & long_name, environment const & env, options const & o);
    json serialize_decl(name const & d, environment const & env, options const & o);
public:
    server(unsigned num_threads, environment const & intial_env, io_state const & ios);
    ~server();

    std::tuple<std::string, module_src, time_t> load_module(module_id const & id, bool can_use_olean) override;

    void run();
};

void initialize_server();
void finalize_server();

}
