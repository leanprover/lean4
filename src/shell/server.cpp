/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_JSON)
#include <list>
#include <string>
#include <vector>
#include <algorithm>
#include <clocale>
#include <library/library_task_builder.h>
#include "util/sexpr/option_declarations.h"
#include "util/timer.h"
#include "library/mt_task_queue.h"
#include "library/st_task_queue.h"
#include "library/attribute_manager.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/interactive.h"
#include "shell/server.h"

namespace lean {
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

bool region_of_interest::intersects(log_tree::node const & n) const {
    if (m_files.empty()) return true;
    if (n.get_location().m_file_name.empty()) return true;
    auto & l = n.get_location();
    if (auto f = m_files.find(l.m_file_name)) {
        return std::max(f->m_begin_line, l.m_range.m_begin.first)
            <= std::min(f->m_end_line, l.m_range.m_end.first);
    } else {
        return false;
    }
}

bool region_of_interest::intersects(message const & msg) const {
    if (m_files.empty()) return true;
    if (auto f = m_files.find(msg.get_file_name())) {
        return f->m_begin_line <= msg.get_pos().first && msg.get_pos().first <= f->m_end_line;
    } else {
        return false;
    }
}

class server::message_handler {
    server * m_srv;
    log_tree * m_lt;

    mutex m_mutex;
    std::unordered_set<std::string> m_dirty_files;
    bool m_full_refresh_scheduled = false;
    std::unique_ptr<single_timer> m_timer;

public:
    message_handler(server * srv, log_tree * lt, bool use_timer) : m_srv(srv), m_lt(lt) {
        if (use_timer) m_timer.reset(new single_timer);
    }

    static void get_messages(log_tree::node const & n, std::vector<message> & msgs, region_of_interest const & roi) {
        if (!roi.intersects(n)) return;
        for (auto & e : n.get_entries()) {
            if (auto msg = dynamic_cast<message const *>(e.get())) {
                if (roi.intersects(*msg))
                    msgs.push_back(*msg);
            }
        }
        n.get_children().for_each([&] (name const &, log_tree::node const & c) {
            get_messages(c, msgs, roi);
        });
    }

    std::vector<message> get_messages_core(region_of_interest const & roi) {
        std::vector<message> msgs;
        get_messages(m_lt->get_root(), msgs, roi);
        return msgs;
    }

    void schedule_refresh() {
#if defined(LEAN_MULTI_THREAD)
        if (m_timer) {
            m_full_refresh_scheduled = true;
            m_timer->set(chrono::steady_clock::now() + chrono::milliseconds(100), [&] {
                    unique_lock<mutex> lock(m_mutex);
                    m_full_refresh_scheduled = false;
                    m_dirty_files.clear();
                    auto roi = m_srv->get_roi();
                    lock.unlock();

                    m_srv->send_msg(all_messages_msg{get_messages_core(roi)});
                }, false);
        }
#endif
        if (!m_full_refresh_scheduled) {
            m_dirty_files.clear();
            m_srv->send_msg(all_messages_msg{get_messages_core(m_srv->get_roi())});
        }
    }

    void on_event(std::vector<log_tree::event> const & events) {
        unique_lock<mutex> lock(m_mutex);
        auto roi = m_srv->get_roi();
        for (auto & e : events) {
            switch (e.m_kind) {
                case log_tree::event::EntryAdded:
                case log_tree::event::EntryRemoved:
                    if (auto msg = dynamic_cast<message const *>(e.m_entry.get())) {
                        if (roi.intersects(*msg)) {
                            m_dirty_files.insert(msg->get_file_name());
                        }
                    }
                    break;

                default: break;
            }
        }
        if (!m_dirty_files.empty()) {
            schedule_refresh();
        }
    }

    void on_new_roi() {
        unique_lock<mutex> lock(m_mutex);
        schedule_refresh();
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

    static json json_of_task(log_tree::node const & t) {
        json j;
        j["file_name"] = t.get_location().m_file_name;
        auto pos = t.get_location().m_range.m_begin;
        j["pos_line"] = pos.first;
        j["pos_col"] = pos.second;
        auto end_pos = t.get_location().m_range.m_end;
        j["end_pos_line"] = end_pos.first;
        j["end_pos_col"] = end_pos.second;
        j["desc"] = t.get_description();
        return j;
    }
};

class server::tasks_handler {
    server * m_srv;
    log_tree * m_lt;

    mutex m_mutex;
    std::unique_ptr<single_timer> m_timer;

public:
    tasks_handler(server * srv, log_tree * lt, bool use_timer) : m_srv(srv), m_lt(lt) {
        if (use_timer) m_timer.reset(new single_timer);
    }

    void mk_tasks_msg(log_tree::node const & n, current_tasks_msg & msg, region_of_interest const & roi) {
        if (!roi.intersects(n)) return;
        if (n.get_producer()) {
            msg.m_is_running = true;
            msg.m_tasks.push_back(current_tasks_msg::json_of_task(n));
            return;
        }
        n.get_children().for_each([&] (name const &, log_tree::node const & c) {
            mk_tasks_msg(c, msg, roi);
        });
    }

    void submit_core(log_tree::node const & n) {
        // TODO(gabriel): priorities
        if (auto prod = n.get_producer()) {
            taskq().submit(prod);
        }
    }

    void resubmit_core(log_tree::node const & n, region_of_interest const & roi) {
        if (!roi.intersects(n)) return;
        submit_core(n);
        n.get_children().for_each([&] (name const &, log_tree::node const & c) {
            resubmit_core(c, roi);
        });
    }
    void resubmit_core() {
        resubmit_core(m_srv->m_lt.get_root(), m_srv->get_roi());
    }

    current_tasks_msg mk_tasks_msg() {
        current_tasks_msg msg;
        mk_tasks_msg(m_lt->get_root(), msg, m_srv->get_roi());
        return msg;
    }

    void schedule_refresh() {
#if defined(LEAN_MULTI_THREAD)
        if (m_timer) {
            m_timer->set(chrono::steady_clock::now() + chrono::milliseconds(200), [&] {
                m_srv->send_msg(mk_tasks_msg());
            }, false);
        }
#endif
    }

    void on_event(std::vector<log_tree::event> const & events) {
        optional<region_of_interest> roi;
        bool need_refresh = false;
        for (auto & e : events) {
            switch (e.m_kind) {
                case log_tree::event::ProducerSet:
                    if (!roi) roi = m_srv->get_roi();
                    if (roi->intersects(e.m_node)) {
                        submit_core(e.m_node);
                        need_refresh = true;
                    }
                    break;
                case log_tree::event::Finished:
                    if (!roi) roi = m_srv->get_roi();
                    if (roi->intersects(e.m_node))
                        need_refresh = true;
                    break;

                default:
                    break;
            }
        }
        if (need_refresh) {
            unique_lock<mutex> lock(m_mutex);
            schedule_refresh();
        }
    }

    void on_new_roi() {
        resubmit_core();
        unique_lock<mutex> lock(m_mutex);
        schedule_refresh();
    }
};

server::server(unsigned num_threads, environment const & initial_env, io_state const & ios) :
        m_initial_env(initial_env), m_ios(ios) {
    m_ios.set_regular_channel(std::make_shared<stderr_channel>());
    m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());

    m_msg_handler.reset(new message_handler(this, &m_lt, num_threads > 0));
    m_tasks_handler.reset(new tasks_handler(this, &m_lt, num_threads > 0));

    m_lt.add_listener([&] (std::vector<log_tree::event> const & evs) {
        m_msg_handler->on_event(evs);
        m_tasks_handler->on_event(evs);
    });

    scope_global_ios scoped_ios(m_ios);
#if defined(LEAN_MULTI_THREAD)
    if (num_threads == 0) {
        m_tq.reset(new st_task_queue);
    } else {
        m_tq.reset(new mt_task_queue(num_threads));
    }
#else
    m_tq.reset(new st_task_queue());
#endif

    set_task_queue(m_tq.get());
    m_mod_mgr.reset(new module_mgr(this, m_lt.get_root(), m_initial_env, m_ios));
    m_mod_mgr->set_use_snapshots(true);
    m_mod_mgr->set_save_olean(false);
}

server::~server() {
    m_mod_mgr->cancel_all();
    cancel(m_bg_task_ctok);
    m_tq->evacuate();
}

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
    scope_global_ios scoped_ios(m_ios);

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
    } catch (std::exception & ex) {
        send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
    }
}

void server::handle_request(server::cmd_req const & req) {
    std::string command = req.m_cmd_name;

    if (command == "sync") {
        send_msg(handle_sync(req));
    } else if (command == "complete") {
        handle_complete(req);
    } else if (command == "info") {
        handle_info(req);
    } else if (command == "roi") {
        send_msg(handle_roi(req));
    } else if (command == "sleep") {
        chrono::milliseconds small_delay(1000);
        this_thread::sleep_for(small_delay);
    } else if (command == "long_sleep") {
        chrono::milliseconds small_delay(10000);
        this_thread::sleep_for(small_delay);
    } else {
        send_msg(cmd_res(req.m_seq_num, std::string("unknown command")));
    }
}

server::cmd_res server::handle_sync(server::cmd_req const & req) {
    std::string new_file_name = req.m_payload.at("file_name");
    std::string new_content = req.m_payload.at("content");

    auto mtime = time(nullptr);

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
        res["message"] = "file invalidated";
    } else {
        res["message"] = "file unchanged";
    }

    return { req.m_seq_num, res };
}

std::shared_ptr<snapshot const> get_closest_snapshot(std::shared_ptr<module_info const> const & mod_info, pos_info p) {
    auto ret = std::shared_ptr<snapshot const>();
    if (auto res = peek(mod_info->m_result)) {
        auto snapshots = res->m_snapshots;
        if (snapshots.size()) {
            ret = snapshots.front();
            for (auto &snap : snapshots) {
                if (snap->m_pos < p)
                    ret = snap;
            }
        }
    }
    return ret;
}

void parse_breaking_at_pos(module_id const & mod_id, std::shared_ptr<module_info const> mod_info, pos_info pos,
                           bool complete = false) {
    std::istringstream in(*mod_info->m_lean_contents);
    if (auto snap = get_closest_snapshot(mod_info, pos)) {
        snapshot s = *snap;

        // ignore messages from reparsing
        log_tree null;
        scope_log_tree scope_lt(null.get_root());

        bool use_exceptions = true;
        parser p(s.m_env, get_global_ios(), mk_dummy_loader(), in, mod_id,
                 use_exceptions, std::make_shared<snapshot>(s), nullptr);
        p.set_break_at_pos(pos);
        p.set_complete(complete);
        p();
    }
}

json server::autocomplete(std::shared_ptr<module_info const> const & mod_info, bool skip_completions,
                          pos_info const & pos0) {
    auto pos = pos0;
    if (pos.second == 0)
        pos.first--;
    pos.second--;
    json j;

    if (auto snap = get_closest_snapshot(mod_info, pos)) {
        try {
            parse_breaking_at_pos(mod_info->m_mod, mod_info, pos, true);
        } catch (break_at_pos_exception & e) {
            report_completions(snap->m_env, snap->m_options, pos, skip_completions, mod_info->m_mod.c_str(),
                               e, j);
        } catch (throwable & ex) {}
    }
    return j;
}

void server::handle_complete(cmd_req const & req) {
    cancel(m_bg_task_ctok);
    m_bg_task_ctok = mk_cancellation_token();

    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};
    bool skip_completions = false;
    if (req.m_payload.count("skip_completions"))
        skip_completions = req.m_payload.at("skip_completions");

    auto mod_info = m_mod_mgr->get_module(fn);

    auto complete_gen_task =
        task_builder<json>([=] { return autocomplete(mod_info, skip_completions, pos); })
        .set_cancellation_token(m_bg_task_ctok)
//        .wrap(library_scopes())
        .build();

    taskq().submit(task_builder<unit>([this, req, complete_gen_task] {
        try {
            send_msg(cmd_res(req.m_seq_num, get(complete_gen_task)));
        } catch (throwable & ex) {
            send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
        }
        return unit{};
    }).depends_on(complete_gen_task).ignore_dependency_errors().build());
}

static void get_info_managers(log_tree::node const & n, std::vector<info_manager> & infoms) {
    for (auto & e : n.get_entries()) {
        if (auto infom = dynamic_cast<info_manager const *>(e.get())) {
            infoms.push_back(*infom);
        }
    }
    n.get_children().for_each([&] (name const &, log_tree::node const & c) {
        get_info_managers(c, infoms);
    });
}

std::vector<info_manager> get_info_managers(log_tree const & t) {
    std::vector<info_manager> infoms;
    get_info_managers(t.get_root(), infoms);
    return infoms;
}

json server::info(std::shared_ptr<module_info const> const & mod_info, pos_info const & pos) {
    json j;
    try {
        parse_breaking_at_pos(mod_info->m_mod, mod_info, pos);
    } catch (break_at_pos_exception & e) {
        auto opts = m_ios.get_options();
        auto env = m_initial_env;
        if (auto snap = get_closest_snapshot(mod_info, e.m_token_info.m_pos)) {
            env = snap->m_env;
            opts = snap->m_options;
        }
        report_info(env, opts, m_ios, *mod_info, get_info_managers(m_lt), e, j);
    } catch (throwable & ex) {}

    return j;
}

void server::handle_info(server::cmd_req const & req) {
    cancel(m_bg_task_ctok);
    m_bg_task_ctok = mk_cancellation_token();

    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};

    auto mod_info = m_mod_mgr->get_module(fn);

    auto info_gen_task = task_builder<json>([=] {
        return info(mod_info, pos);
    }).depends_on(mk_deep_dependency(
        mod_info->m_result, [] (buffer<gtask> & deps, module_info::parse_result const & res) {
            deps.push_back(res.m_loaded_module->m_env);
    })).set_cancellation_token(m_bg_task_ctok)
//       .wrap(library_scopes())
       .build();

    taskq().submit(task_builder<unit>([this, req, info_gen_task] {
        try {
            send_msg(cmd_res(req.m_seq_num, get(info_gen_task)));
        } catch (throwable & ex) {
            send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
        }
        return unit{};
    }).depends_on(info_gen_task).ignore_dependency_errors().build());
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

region_of_interest server::get_roi() {
    unique_lock<mutex> _(m_roi_mutex);
    return m_roi;
}

server::cmd_res server::handle_roi(server::cmd_req const & req) {
    region_of_interest new_roi;
    for (auto & f : req.m_payload.at("files")) {
        std::string fn = f.at("file_name");
        unsigned begin_line = f.at("begin_line");
        unsigned end_line = f.at("end_line");
        new_roi.m_files.insert(fn, line_range {begin_line, end_line});
    }
    new_roi.m_files.for_each([&] (std::string const & fn, line_range const &) {
        try { m_mod_mgr->get_module(fn); } catch (...) {}
    });
    {
        unique_lock<mutex> _(m_roi_mutex);
        m_roi = new_roi;
    }
    m_tasks_handler->on_new_roi();
    m_msg_handler->on_new_roi();

    return cmd_res(req.m_seq_num, json());
}

void initialize_server() {
}

void finalize_server() {
}

}
#endif
