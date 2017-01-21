/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_JSON)
#include <list>
#include <string>
#include <algorithm>
#include <vector>
#include <clocale>
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "util/utf8.h"
#include "library/mt_task_queue.h"
#include "library/st_task_queue.h"
#include "library/attribute_manager.h"
#include "library/tactic/tactic_state.h"
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

struct msg_reported_msg {
    message m_msg;

    json to_json_response() const {
        json j;
        j["response"] = "additional_message";
        j["msg"] = json_of_message(m_msg);
        return j;
    }
};

struct all_messages_msg {
    std::vector<message> m_msgs;

    json to_json_response() const {
        auto msgs = json::array();
        for (auto & msg : m_msgs)
            msgs.push_back(json_of_message(msg));

        json j;
        j["response"] = "all_messages";
        j["msgs"] = msgs;
        return j;
    }
};

class server::msg_buf : public versioned_msg_buf {
    server * m_srv;

    std::unordered_set<name, name_hash> m_nonempty_buckets;

public:
    msg_buf(server * srv) : m_srv(srv) {}

    void on_cleared(name const & bucket) override {
        if (m_nonempty_buckets.count(bucket)) {
            m_nonempty_buckets.clear();
            for (auto & b : get_nonempty_buckets_core()) m_nonempty_buckets.insert(b);

            // We need to remove a message, so let's send everything again
            m_srv->send_msg(all_messages_msg{get_messages_core()});
        }
    }

    void on_reported(name const & bucket, message const & msg) override {
        m_nonempty_buckets.insert(bucket);
        m_srv->send_msg(msg_reported_msg{msg});
    }
};

struct current_tasks_msg {
    std::vector<json> m_tasks;
    optional<json> m_cur_task;
    bool m_is_running = false;

    json to_json_response() const {
        json j;
        j["response"] = "current_tasks";
        j["is_running"] = m_is_running;
        if (m_cur_task) j["cur_task"] = *m_cur_task;
        j["tasks"] = m_tasks;
        return j;
    }

    json json_of_task(generic_task const * t) {
        json j;
        j["file_name"] = t->get_module_id();
        auto pos = t->get_pos();
        j["pos_line"] = pos.first;
        j["pos_col"] = pos.second;
        auto end_pos = t->get_end_pos();
        j["end_pos_line"] = end_pos.first;
        j["end_pos_col"] = end_pos.second;
        j["desc"] = t->description();
        return j;
    }

#if defined(LEAN_MULTI_THREAD)
    current_tasks_msg(mt_tq_status const & st, std::unordered_set<std::string> const & visible_files) {
        m_is_running = st.size() > 0;
        st.for_each([&] (generic_task const * t) {
            if (!t->is_tiny() && visible_files.count(t->get_module_id())) {
                auto j = json_of_task(t);
                if (!m_cur_task) m_cur_task = {j};
                m_tasks.push_back(j);
            }
        });
    }
#endif
};

server::server(unsigned num_threads, environment const & initial_env, io_state const & ios) :
        m_initial_env(initial_env), m_ios(ios) {
    m_ios.set_regular_channel(std::make_shared<stderr_channel>());
    m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());

    m_msg_buf.reset(new msg_buf(this));

    scope_global_ios scoped_ios(m_ios);
    scoped_message_buffer scope_msg_buf(m_msg_buf.get());
#if defined(LEAN_MULTI_THREAD)
    if (num_threads == 0) {
        m_tq.reset(new st_task_queue());
    } else {
        auto tq = new mt_task_queue(num_threads);
        m_tq.reset(tq);
        tq->set_monitor_interval(chrono::milliseconds(300));
        tq->set_status_callback([this] (mt_tq_status const & st) {
            unique_lock<mutex> _(m_visible_files_mutex);
            send_msg(current_tasks_msg(st, m_visible_files));
        });
    }
#else
    m_tq.reset(new st_task_queue());
#endif

    scope_global_task_queue scope_tq(m_tq.get());
    m_mod_mgr.reset(new module_mgr(this, m_msg_buf.get(), m_initial_env, m_ios));
    m_mod_mgr->set_use_snapshots(true);
    m_mod_mgr->set_save_olean(false);
}

server::~server() {}

struct server::cmd_req {
    unsigned m_seq_num = static_cast<unsigned>(-1);
    std::string m_cmd_name;
    json m_payload;
};

struct server::cmd_res {
    cmd_res() {}
    cmd_res(unsigned seq_num, json const & payload) : m_seq_num(seq_num), m_payload(payload) {}
    cmd_res(unsigned seq_num, std::string const & error_msg) : m_seq_num(seq_num), m_error_msg(error_msg) {}

    unsigned m_seq_num = static_cast<unsigned>(-1);
    json m_payload;
    optional<std::string> m_error_msg;

    json to_json_response() const {
        json j;
        if (m_error_msg) {
            j["response"] = "error";
            j["message"] = *m_error_msg;
        } else {
            j = m_payload;
            j["response"] = "ok";
        }
        j["seq_num"] = m_seq_num;
        return j;
    }
};

struct unrelated_error_msg {
    std::string m_msg;

    json to_json_response() const {
        json j;
        j["response"] = "error";
        j["message"] = m_msg;
        return j;
    }
};

void server::run() {
    scope_global_task_queue scope_tq(m_tq.get());
    scope_global_ios scoped_ios(m_ios);
    scoped_message_buffer scope_msg_buf(m_msg_buf.get());

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

            handle_request(req);
        } catch (std::exception & ex) {
            send_msg(unrelated_error_msg{ex.what()});
        }
    }
}

void server::handle_request(json const & jreq) {
    cmd_req req;
    req.m_seq_num = jreq.at("seq_num");
    try {
        req.m_cmd_name = jreq.at("command");
        req.m_payload = jreq;
        handle_request(req);
    } catch (throwable & ex) {
        send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
    }
}

void server::handle_request(server::cmd_req const & req) {
    std::string command = req.m_cmd_name;

    if (command == "sync") {
        return send_msg(handle_sync(req));
    } else if (command == "complete") {
        return handle_complete(req);
    } else if (command == "info") {
        return handle_info(req);
    }

    send_msg(cmd_res(req.m_seq_num, std::string("unknown command")));
}

server::cmd_res server::handle_sync(server::cmd_req const & req) {
    std::string new_file_name = req.m_payload.at("file_name");
    std::string new_content = req.m_payload.at("content");

    auto mtime = time(nullptr);

#if defined(LEAN_MULTI_THREAD)
    {
        unique_lock<mutex> _(m_visible_files_mutex);
        if (m_visible_files.count(new_file_name) == 0) {
            m_visible_files.insert(new_file_name);
            if (auto tq = dynamic_cast<mt_task_queue *>(m_tq.get()))
                tq->reprioritize(mk_interactive_prioritizer(m_visible_files));
        }
    }
#endif

    bool needs_invalidation = !m_open_files.count(new_file_name);

    auto & ef = m_open_files[new_file_name];
    if (ef.m_content != new_content) {
        ef.m_content = new_content;
        ef.m_mtime = mtime;
        needs_invalidation = true;
    }

    json res;
    if (needs_invalidation) {
        m_mod_mgr->invalidate(new_file_name);
        try { m_mod_mgr->get_module(new_file_name); } catch (...) {}
        res["message"] = "file invalidated";
    } else {
        res["message"] = "file unchanged";
    }

    return { req.m_seq_num, res };
}

std::shared_ptr<snapshot const> get_closest_snapshot(std::shared_ptr<module_info const> const & mod_info, pos_info p) {
    auto snapshots = mod_info.get()->m_result.get().m_snapshots;
    auto ret = snapshots.size() ? snapshots.front() : std::shared_ptr<snapshot>();
    for (auto & snap : snapshots) {
        if (snap->m_pos < p)
            ret = snap;
    }
    return ret;
}

void parse_breaking_at_pos(module_id const & mod_id, std::shared_ptr<module_info const> mod_info, pos_info pos,
                           bool complete = false) {
    std::istringstream in(*mod_info->m_lean_contents);
    if (auto snap = get_closest_snapshot(mod_info, pos)) {
        snapshot s = *snap;
        s.m_sub_buckets.clear(); // HACK

        // ignore messages from reparsing
        null_message_buffer null_msg_buf;
        scoped_message_buffer scope(&null_msg_buf);

        bool use_exceptions = true;
        parser p(s.m_env, get_global_ios(), mk_dummy_loader(), in, mod_id,
                 use_exceptions, std::make_shared<snapshot>(s), nullptr);
        p.set_break_at_pos(pos);
        p.set_complete(complete);
        p();
    }
}

class server::auto_complete_task : public task<unit> {
    server * m_server;
    unsigned m_seq_num;
    std::shared_ptr<module_info const> m_mod_info;
    bool     m_skip_completions;

public:
    auto_complete_task(server * server, unsigned seq_num, std::shared_ptr<module_info const> const & mod_info,
                       bool skip_completions) :
        m_server(server), m_seq_num(seq_num), m_mod_info(mod_info), m_skip_completions(skip_completions) {}

    // TODO(gabriel): find cleaner way to give it high prio
    task_kind get_kind() const override { return task_kind::parse; }

    virtual bool is_tiny() const override { return true; }

    void description(std::ostream & out) const override {
        out << "generating auto-completion at (" << get_pos().first << ", " << get_pos().second << ")";
    }

    std::vector<generic_task_result> get_dependencies() override {
        return {m_mod_info->m_result};
    }

    // TODO(gabriel): handle cancellation

    unit execute() override {
        try {
            pos_info pos = get_pos();
            if (pos.second == 0)
                pos.first--;
            pos.second--;
            json j;

            if (auto snap = get_closest_snapshot(m_mod_info, pos)) {
                try {
                    parse_breaking_at_pos(get_module_id(), m_mod_info, pos, true);
                } catch (break_at_pos_exception & e) {
                    unsigned offset = get_pos().second - e.m_token_info.m_pos.second;
                    std::string prefix = e.m_token_info.m_token.to_string();
                    if (auto stop = utf8_char_pos(prefix.c_str(), offset))
                        prefix = prefix.substr(0, *stop);
                    switch (e.m_token_info.m_context) {
                        case break_at_pos_exception::token_context::expr:
                            // no empty prefix completion for declarations
                            if (!prefix.size()) {
                                m_server->send_msg(cmd_res(m_seq_num, j));
                                return {};
                            }
                            if (!m_skip_completions)
                                j["completions"] = get_decl_completions(prefix, snap->m_env, snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::field:
                            if (!m_skip_completions)
                                j["completions"] = get_field_completions(e.m_token_info.m_struct, prefix, snap->m_env, snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::option:
                            if (!m_skip_completions)
                                j["completions"] = get_option_completions(prefix, snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::import:
                            if (!m_skip_completions)
                                j["completions"] = get_import_completions(prefix, dirname(m_mod_info->m_mod.c_str()),
                                                                          snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::interactive_tactic:
                            if (!m_skip_completions)
                                j["completions"] = get_interactive_tactic_completions(
                                        prefix, e.m_token_info.m_tac_class, snap->m_env, snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::attribute:
                            if (!m_skip_completions)
                                j["completions"] = get_attribute_completions(prefix, snap->m_env, snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::namespc:
                            if (!m_skip_completions)
                                j["completions"] = get_namespace_completions(prefix, snap->m_env, snap->m_options);
                            break;
                        case break_at_pos_exception::token_context::none:
                        case break_at_pos_exception::token_context::notation:
                            m_server->send_msg(cmd_res(m_seq_num, j));
                            return {};
                    }
                    j["prefix"] = prefix;
                } catch (throwable & ex) {}
            }

            m_server->send_msg(cmd_res(m_seq_num, j));
        } catch (throwable & ex) {
            m_server->send_msg(cmd_res(m_seq_num, std::string(ex.what())));
        }
        return {};
    }
};

void server::handle_complete(cmd_req const & req) {
    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};
    bool skip_completions = false;
    if (req.m_payload.count("skip_completions"))
        skip_completions = req.m_payload.at("skip_completions");

    scope_message_context scope_msg_ctx(message_bucket_id { "_server", 0 });
    scoped_task_context scope_task_ctx(fn, pos);

    auto mod_info = m_mod_mgr->get_module(fn);

    get_global_task_queue()->submit<auto_complete_task>(this, req.m_seq_num, mod_info, skip_completions);
}

class server::info_task : public task<unit> {
    server * m_server;
    unsigned m_seq_num;
    std::shared_ptr<module_info const> m_mod_info;

public:
    info_task(server * server, unsigned seq_num, std::shared_ptr<module_info const> const & mod_info):
            m_server(server), m_seq_num(seq_num), m_mod_info(mod_info) {}

    // TODO(gabriel): find cleaner way to give it high prio
    task_kind get_kind() const override { return task_kind::parse; }

    virtual bool is_tiny() const override { return true; }

    void description(std::ostream & out) const override {
        out << "info at (" << get_pos().first << ", " << get_pos().second << ")";
    }

    std::vector<generic_task_result> get_dependencies() override {
        std::vector<generic_task_result> deps;
        deps.push_back(m_mod_info->m_result);
        if (auto mod = m_mod_info->m_result.peek()) {
            deps.push_back(mod->m_loaded_module->m_env);
        }
        return deps;
    }

    // TODO(gabriel): handle cancellation

    unit execute() override {
        try {
            pos_info pos = get_pos();
            json j;
            try {
                parse_breaking_at_pos(get_module_id(), m_mod_info, pos);
            } catch (break_at_pos_exception & e) {
                json record;

                auto opts = m_server->m_ios.get_options();
                auto env = m_server->m_initial_env;
                if (auto mod = m_mod_info->m_result.peek()) {
                    if (mod->m_loaded_module->m_env)
                        env = mod->m_loaded_module->m_env.get();
                    if (!mod->m_snapshots.empty()) opts = mod->m_snapshots.back()->m_options;
                }

                // info data not dependent on elaboration/info_manager
                auto const & tk = e.m_token_info.m_token;
                if (tk.size()) {
                    switch (e.m_token_info.m_context) {
                        case break_at_pos_exception::token_context::attribute:
                            record["doc"] = get_attribute(env, tk).get_description();
                            add_source_info(env, tk, record);
                            break;
                        case break_at_pos_exception::token_context::import: {
                            auto parsed = parse_import(tk.to_string());
                            try {
                                auto f = find_file(m_mod_info->m_mod, parsed.first, string_to_name(parsed.second),
                                                   ".lean");
                                record["source"]["file"] = f;
                                record["source"]["line"] = 1;
                                record["source"]["column"] = 0;
                            } catch (file_not_found_exception) {}
                            break;
                        }
                        case break_at_pos_exception::token_context::option:
                            if (auto it = get_option_declarations().find(tk))
                                record["doc"] = it->get_description();
                            break;
                        default:
                            break;
                    }
                }

                for (auto & infom : m_server->m_msg_buf->get_info_managers()) {
                    if (infom.get_file_name() == get_module_id()) {
                        infom.get_info_record(env, opts, m_server->m_ios, e.m_token_info.m_pos.first,
                                              e.m_token_info.m_pos.second, record);
                        if (e.m_goal_pos) {
                            infom.get_info_record(env, opts, m_server->m_ios, e.m_goal_pos->first,
                                                  e.m_goal_pos->second, record, [](info_data const & d) {
                                        return dynamic_cast<vm_obj_format_info const *>(d.raw());
                                    });
                        }
                    }
                }

                if (!record.is_null())
                    j["record"] = record;
            } catch (throwable & ex) {}

            m_server->send_msg(cmd_res(m_seq_num, j));
        } catch (throwable & ex) {
            m_server->send_msg(cmd_res(m_seq_num, std::string(ex.what())));
        }
        return {};
    }
};

void server::handle_info(server::cmd_req const & req) {
    m_info_result.cancel();

    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};

    scope_message_context scope_msg_ctx(message_bucket_id { "_server", 0 });
    scoped_task_context scope_task_ctx(fn, pos);

    auto mod_info = m_mod_mgr->get_module(fn);

    m_info_result = {get_global_task_queue()->submit<info_task>(this, req.m_seq_num, mod_info)};
}

std::tuple<std::string, module_src, time_t> server::load_module(module_id const & id, bool can_use_olean) {
    if (m_open_files.count(id)) {
        auto & ef = m_open_files[id];
        return std::make_tuple(ef.m_content, module_src::LEAN, ef.m_mtime);
    }
    return m_fs_vfs.load_module(id, can_use_olean);
}

template <class Msg>
void server::send_msg(Msg const & m) {
    json j = m.to_json_response();
    unique_lock<mutex> _(m_out_mutex);
    std::cout << j << std::endl;
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
mt_tq_prioritizer mk_interactive_prioritizer(std::unordered_set<module_id> const & roi) {
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

        bool in_roi = roi.count(t->get_module_id()) > 0;

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
