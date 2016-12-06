/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_SERVER)
#include <list>
#include <string>
#include <algorithm>
#include <vector>
#include <clocale>
#include "util/sexpr/option_declarations.h"
#include "library/mt_task_queue.h"
#include "library/st_task_queue.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"
#include "shell/server.h"
#include "shell/completion.h"

#ifndef LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS
#define LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS 100
#endif

namespace lean {
static name * g_auto_completion_max_results = nullptr;

unsigned get_auto_completion_max_results(options const & o) {
    return o.get_unsigned(*g_auto_completion_max_results, LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS);
}

server::server(unsigned num_threads, environment const & initial_env, io_state const & ios) :
        m_initial_env(initial_env), m_ios(ios) {
    m_ios.set_regular_channel(std::make_shared<stderr_channel>());
    m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());

    scope_global_ios scoped_ios(m_ios);
    scoped_message_buffer scope_msg_buf(&m_msg_buf);
#if defined(LEAN_MULTI_THREAD)
    if (num_threads == 0)
        m_tq = new st_task_queue;
    else
        m_tq = new mt_task_queue(num_threads);
#else
    m_tq = new st_task_queue;
#endif

    scope_global_task_queue scope_tq(m_tq);
    m_mod_mgr = new module_mgr(this, &m_msg_buf, m_initial_env, m_ios);
    m_mod_mgr->set_use_snapshots(true);
    m_mod_mgr->set_save_olean(false);
}

server::~server() {
    delete m_tq;
    delete m_mod_mgr;
}

void server::run() {
    scope_global_task_queue scope_tq(m_tq);
    scope_global_ios scoped_ios(m_ios);
    scoped_message_buffer scope_msg_buf(&m_msg_buf);

    /* Leo: we use std::setlocale to make sure decimal period is displayed as ".".
       We added this hack because the json library code used for ensuring this property
       was crashing when compiling Lean on Windows with mingw. */
#if !defined(LEAN_EMSCRIPTEN)
    std::setlocale(LC_NUMERIC, "C");
#endif

    while (true) {
        try {
            std::string req_string;
            std::getline(std::cin, req_string);
            if (std::cin.eof()) return;

            json req = json::parse(req_string);

            json res = handle_request(req);
            std::cout << res << std::endl;
        } catch (std::exception & ex) {
            json res;
            res["response"] = "error";
            res["message"] = ex.what();
            std::cout << res << std::endl;
        }
    }
}

json server::handle_request(json const & req) {
    std::string command = req["command"];

    if (command == "sync") {
        return handle_sync(req);
    } else if (command == "check") {
        return handle_check(req);
    } else if (command == "complete") {
        return handle_complete(req);
    } else if (command == "info") {
        return handle_info(req);
    }

    json res;
    res["response"] = "error";
    res["message"] = "unknown command";
    return res;
}

json server::handle_sync(json const & req) {
    std::string new_file_name = req["file_name"];
    std::string new_content = req["content"];

    json res;
    res["response"] = "ok";

    auto mtime = time(nullptr);

#if defined(LEAN_MULTI_THREAD)
    if (m_visible_file != new_file_name) {
        if (auto tq = dynamic_cast<mt_task_queue *>(m_tq))
            tq->reprioritize(mk_interactive_prioritizer(new_file_name));
        m_visible_file = new_file_name;
    }
#endif

    bool needs_invalidation = !m_open_files.count(new_file_name);

    auto & ef = m_open_files[new_file_name];
    if (ef.m_content != new_content) {
        ef.m_content = new_content;
        ef.m_mtime = mtime;
        needs_invalidation = true;
    }

    if (needs_invalidation) {
        m_mod_mgr->invalidate(new_file_name);
        res["message"] = "file invalidated";
    }

    return res;
}

json server::handle_check(json const &) {
    bool incomplete = !get_global_task_queue().empty(); // TODO(gabriel)

    std::list<json> json_messages;
    for (auto & msg : m_msg_buf.get_messages()) {
        json_messages.push_back(json_of_message(msg));
    }

    json res;
    res["response"] = "ok";
    res["incomplete"] = incomplete;
    res["incomplete_reason"] = "";
    if (auto cur_task = get_global_task_queue().get_current_task())
        res["incomplete_reason"] = cur_task->description();
    res["messages"] = json_messages;
    return res;
}

std::shared_ptr<snapshot const> server::get_closest_snapshot(module_id const & id, unsigned line) {
    auto snapshots = m_mod_mgr->get_snapshots(id);
    auto ret = snapshots.size() ? snapshots.front() : std::shared_ptr<snapshot>();
    for (auto & snap : snapshots) {
        if (snap->m_pos.first <= line)
            ret = snap;
    }
    return ret;
}

json server::handle_complete(json const & req) {
    std::string fn = req["file_name"];
    std::string pattern = req["pattern"];
    unsigned line = req["line"];

    std::vector<json> completions;
    if (auto snap = get_closest_snapshot(fn, line))
        completions = get_completions(pattern, snap->m_env, snap->m_options);

    json res;
    res["response"] = "ok";
    res["completions"] = completions;
    return res;
}

json server::handle_info(json const & req) {
    std::string fn = req["file_name"];
    unsigned line = req["line"];
    unsigned col = req["column"];

    auto opts = m_ios.get_options();
    auto env = m_initial_env;
    if (auto mod = m_mod_mgr->get_module(fn)->m_result.peek()) {
        if (mod->m_env) env = *mod->m_env;
        if (!mod->m_snapshots.empty()) opts = mod->m_snapshots.back()->m_options;
    }

    json record;
    for (auto & infom : m_msg_buf.get_info_managers()) {
        if (infom.get_file_name() == fn) {
            infom.get_info_record(env, opts, m_ios, line, col, record);
        }
    }

    json res;
    res["response"] = "ok";
    res["record"] = record;
    return res;
}

std::tuple<std::string, module_src, time_t> server::load_module(module_id const & id, bool can_use_olean) {
    if (m_open_files.count(id)) {
        auto & ef = m_open_files[id];
        return std::make_tuple(ef.m_content, module_src::LEAN, ef.m_mtime);
    }
    return m_fs_vfs.load_module(id, can_use_olean);
}

void initialize_server() {
    g_auto_completion_max_results = new name{"auto_completion", "max_results"};
    register_unsigned_option(*g_auto_completion_max_results, LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS,
                             "(auto-completion) maximum number of results returned");
}

void finalize_server() {
    delete g_auto_completion_max_results;
}

#if defined(LEAN_MULTI_THREAD)
mt_tq_prioritizer mk_interactive_prioritizer(module_id const & roi) {
    const unsigned
        ROI_PARSING_PRIO = 10,
        ROI_PRINT_PRIO = 11,
        ROI_ELAB_PRIO = 13,
        DEFAULT_PRIO = 20,
        PARSING_PRIO = 20,
        PRINT_PRIO = 21,
        ELAB_PRIO = 23;

    return[=] (generic_task * t) {
        task_priority p;
        p.m_prio = DEFAULT_PRIO;

        bool in_roi = t->get_module_id() == roi;

        if (!in_roi)
            p.m_not_before = { chrono::steady_clock::now() + chrono::seconds(10) };

        switch (t->get_kind()) {
            case task_kind::parse:
                p.m_prio = in_roi ? ROI_PARSING_PRIO : PARSING_PRIO;
                break;
            case task_kind::elab:
                p.m_prio = in_roi ? ROI_ELAB_PRIO : ELAB_PRIO;
                break;
            case task_kind::print:
                p.m_prio = in_roi ? ROI_PRINT_PRIO : PRINT_PRIO;
                break;
        }

        return p;
    };
}
#endif

}
#endif
