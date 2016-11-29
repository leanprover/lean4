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
#include "util/bitap_fuzzy_search.h"
#include "kernel/instantiate.h"
#include "library/mt_task_queue.h"
#include "library/st_task_queue.h"
#include "library/protected.h"
#include "library/scoped_ext.h"
#include "library/type_context.h"
#include "library/module.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/util.h"
#include "shell/server.h"

#ifndef LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS
#define LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS 100
#endif

#define LEAN_FUZZY_MAX_ERRORS          3
#define LEAN_FUZZY_MAX_ERRORS_FACTOR   3
#define LEAN_COMPLETE_CONSUME_IMPLICIT true // lean will add metavariables for implicit arguments in serialize_decl()

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

    m_mtime = time(nullptr);
    if (m_file_name != new_file_name) {
#if defined(LEAN_MULTI_THREAD)
        if (auto tq = dynamic_cast<mt_task_queue *>(m_tq))
            tq->reprioritize(mk_interactive_prioritizer(new_file_name));
#endif
        m_mod_mgr->invalidate(m_file_name);
        m_file_name = new_file_name;
        m_content = new_content;
        res["message"] = "new file name, reloading";
    } else {
        m_content = new_content;
        res["message"] = "file partially invalidated";
    }
    m_mod_mgr->invalidate(m_file_name);
    return res;
}

json server::handle_check(json const &) {
    bool incomplete = !get_global_task_queue().empty(); // TODO(gabriel)

    std::list<json> json_messages;
    for (auto & msg : m_msg_buf.get_messages()) {
        json_messages.push_back(json_of_message(msg));
    }

    bool is_ok = false;
    if (auto res = m_mod_mgr->get_module(m_file_name).m_result.peek()) {
        is_ok = res->m_ok;
    }

    json res;
    res["response"] = "ok";
    res["incomplete"] = incomplete;
    res["incomplete_reason"] = "";
    if (auto cur_task = get_global_task_queue().get_current_task())
        res["incomplete_reason"] = cur_task->description();
    res["is_ok"] = is_ok;
    res["messages"] = json_messages;
    return res;
}

snapshot const * server::get_closest_snapshot(unsigned line) {
    auto snapshots = m_mod_mgr->get_snapshots(m_file_name);
    snapshot const * ret = snapshots.size() ? &snapshots.front() : nullptr;
    for (snapshot const & snap : snapshots) {
        if (snap.m_pos.first <= line)
            ret = &snap;
    }
    return ret;
}

/** \brief Return an (atomic) name if \c n can be referenced by this atomic
    name in the given environment. */
optional<name> is_essentially_atomic(environment const & env, name const & n) {
    if (n.is_atomic())
        return optional<name>(n);
    list<name> const & ns_list = get_namespaces(env);
    for (name const & ns : ns_list) {
        if (is_prefix_of(ns, n)) {
            auto n_prime = n.replace_prefix(ns, name());
            if (n_prime.is_atomic() && !is_protected(env, n))
                return optional<name>(n_prime);
            break;
        }
    }
    if (auto it = is_uniquely_aliased(env, n))
        if (it->is_atomic())
            return it;
    return optional<name>();
}

unsigned get_fuzzy_match_max_errors(unsigned prefix_sz) {
    unsigned r = (prefix_sz / LEAN_FUZZY_MAX_ERRORS_FACTOR);
    if (r > LEAN_FUZZY_MAX_ERRORS)
        return LEAN_FUZZY_MAX_ERRORS;
    return r;
}

optional<name> exact_prefix_match(environment const & env, std::string const & pattern, declaration const & d) {
    if (auto it = is_essentially_atomic(env, d.get_name())) {
        std::string it_str = it->to_string();
        // if pattern "perfectly" matches beginning of declaration name, we just display d on the top of the list
        if (it_str.compare(0, pattern.size(), pattern) == 0)
            return it;
    } else {
        std::string d_str = d.get_name().to_string();
        if (d_str.compare(0, pattern.size(), pattern) == 0)
            return optional<name>(d.get_name());
    }
    return optional<name>();
}

json server::serialize_decl(name const & short_name, name const & long_name, environment const & env, options const & o) {
    declaration const & d = env.get(long_name);
    type_context tc(env);
    io_state_stream out   = regular(env, m_ios, tc).update_options(o);
    expr type = d.get_type();
    if (LEAN_COMPLETE_CONSUME_IMPLICIT) {
        while (true) {
            if (!is_pi(type))
                break;
            if (!binding_info(type).is_implicit() && !binding_info(type).is_inst_implicit())
                break;
            std::string q("?");
            q += binding_name(type).to_string();
            expr m = mk_constant(name(q.c_str()));
            type   = instantiate(binding_body(type), m);
        }
    }
    json completion;
    completion["text"] = short_name.to_string();
    std::ostringstream ss;
    ss << mk_pair(flatten(out.get_formatter()(type)), o);
    completion["type"] = ss.str();
    return completion;
}

json server::serialize_decl(name const & d, environment const & env, options const & o) {
    // using namespace override resolution rule
    list<name> const & ns_list = get_namespaces(env);
    for (name const & ns : ns_list) {
        name new_d = d.replace_prefix(ns, name());
        if (new_d != d &&
            !new_d.is_anonymous() &&
            (!new_d.is_atomic() || !is_protected(env, d))) {
            return serialize_decl(new_d, d, env, o);
        }
    }
    // if the alias is unique use it
    if (auto it = is_uniquely_aliased(env, d)) {
        return serialize_decl(*it, d, env, o);
    } else {
        return serialize_decl(d, d, env, o);
    }
}

json server::handle_complete(json const & req) {
    std::string pattern = req["pattern"];
    unsigned line = req["line"];
    std::vector<json> completions;

    if (snapshot const * snap = get_closest_snapshot(line)) {
        environment const & env = snap->m_env;
        options const & opts = snap->m_options;
        unsigned max_results = get_auto_completion_max_results(opts);
        unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
        std::vector<pair<name, name>> exact_matches;
        std::vector<pair<std::string, name>> selected;
        bitap_fuzzy_search matcher(pattern, max_errors);
        env.for_each_declaration([&](declaration const & d) {
            if (is_projection(env, d.get_name()))
                return;
            if (auto it = exact_prefix_match(env, pattern, d)) {
                exact_matches.emplace_back(*it, d.get_name());
            } else {
                std::string text = d.get_name().to_string();
                if (matcher.match(text))
                    selected.emplace_back(text, d.get_name());
            }
        });
        unsigned num_results = 0;
        if (!exact_matches.empty()) {
            std::sort(exact_matches.begin(), exact_matches.end(),
                      [](pair<name, name> const & p1, pair<name, name> const & p2) {
                          return p1.first.size() < p2.first.size();
                      });
            for (pair<name, name> const & p : exact_matches) {
                completions.push_back(serialize_decl(p.first, p.second, env, opts));
                num_results++;
                if (num_results >= max_results)
                    break;
            }
        }
        unsigned sz = selected.size();
        if (sz == 1) {
            completions.push_back(serialize_decl(selected[0].second, env, opts));
        } else if (sz > 1) {
            std::vector<pair<std::string, name>> next_selected;
            for (unsigned k = 0; k <= max_errors && num_results < max_results; k++) {
                bitap_fuzzy_search matcher(pattern, k);
                for (auto const & s : selected) {
                    if (matcher.match(s.first)) {
                        completions.push_back(serialize_decl(s.second, env, opts));
                        num_results++;
                        if (num_results >= max_results)
                            break;
                    } else {
                        next_selected.push_back(s);
                    }
                }
                std::swap(selected, next_selected);
                next_selected.clear();
            }
        }
    }
    json res;
    res["response"] = "ok";
    res["completions"] = completions;
    return res;
}

json server::handle_info(json const & req) {
    unsigned line = req["line"];
    unsigned col = req["column"];

    auto opts = m_ios.get_options();
    auto env = m_initial_env;
    if (auto mod = m_mod_mgr->get_module(m_file_name).m_result.peek()) {
        if (mod->m_env) env = *mod->m_env;
        if (!mod->m_snapshots.empty()) opts = mod->m_snapshots.back().m_options;
    }

    json record;
    for (auto & infom : m_msg_buf.get_info_managers()) {
        if (infom.get_file_name() == m_file_name) {
            infom.get_info_record(env, opts, m_ios, line, col, record);
        }
    }

    json res;
    res["response"] = "ok";
    res["record"] = record;
    return res;
}

std::tuple<std::string, module_src, time_t> server::load_module(module_id const & id, bool can_use_olean) {
    if (id == m_file_name) {
        return std::make_tuple(m_content, module_src::LEAN, m_mtime);
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
