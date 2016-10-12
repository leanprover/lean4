/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "kernel/pos_info_provider.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "shell/json.h"
#include <string>

namespace lean {

class server {
    optional<std::string> m_base_dir;
    unsigned m_num_threads;
    options m_opts;
    environment m_initial_env;
    io_state m_ios;

    std::string m_file_name;
    std::string m_content;
    optional<pos_info> m_only_checked_until;

    json handle_request(json const & req);

    json handle_sync(json const & req);
    json handle_check(json const & req);

public:
    server(optional<std::string> const & base_dir, int num_threads, environment const & intial_env, io_state const & ios);
    ~server();

    void run();
};

}
