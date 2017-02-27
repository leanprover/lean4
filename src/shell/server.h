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
#include "library/module_mgr.h"
#include "frontends/lean/json.h"
#include "library/mt_task_queue.h"
#include "util/cancellable.h"

namespace lean {

unsigned get_auto_completion_max_results(options const &);

struct line_range {
    unsigned m_begin_line = 0, m_end_line = 0;
    line_range() = default;
    line_range(unsigned begin_line, unsigned end_line) : m_begin_line(begin_line), m_end_line(end_line) {}
};

struct string_cmp {
    int operator()(std::string const & s1, std::string const & s2) const {
        return s1.compare(s2);
    }
};

struct region_of_interest {
    bool m_enabled = false;
    rb_map<std::string, line_range, string_cmp> m_files;

    bool intersects(log_tree::node const & n) const;
    bool intersects(message const & msg) const;
};

class server : public module_vfs {
    options m_opts;
    environment m_initial_env;
    io_state m_ios;

    struct editor_file {
        time_t m_mtime;
        std::string m_content;
    };
    std::unordered_map<std::string, editor_file> m_open_files;

    mutex m_roi_mutex;
    region_of_interest m_roi;

    mutex m_out_mutex;

    log_tree m_lt;

    class message_handler;
    std::unique_ptr<message_handler> m_msg_handler;
    class tasks_handler;
    std::unique_ptr<tasks_handler> m_tasks_handler;

    std::unique_ptr<module_mgr> m_mod_mgr;
    std::unique_ptr<task_queue> m_tq;
    fs_module_vfs m_fs_vfs;

    cancellation_token m_bg_task_ctok;

    template <class Msg>
    void send_msg(Msg const &);

    struct cmd_res;
    struct cmd_req;
    void handle_request(cmd_req const & req);

    cmd_res handle_sync(cmd_req const & req);
    class auto_complete_task;
    void handle_complete(cmd_req const & req);
    class info_task;
    void handle_info(cmd_req const & req);
    cmd_res handle_roi(cmd_req const & req);

    json autocomplete(std::shared_ptr<module_info const> const & mod_info, bool skip_completions, pos_info const & pos);
    json info(std::shared_ptr<module_info const> const & mod_info, pos_info const & pos);

public:
    server(unsigned num_threads, environment const & intial_env, io_state const & ios);
    ~server();

    std::tuple<std::string, module_src, time_t> load_module(module_id const & id, bool can_use_olean) override;

    void run();
    void handle_request(json const & req);

    log_tree & get_log_tree() { return m_lt; }

    region_of_interest get_roi();
};

void initialize_server();
void finalize_server();

}
