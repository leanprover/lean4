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
#include "frontends/lean/parser.h"
#include "library/module.h"
#include "shell/server.h"
#include "frontends/lean/info_manager.h"
#include "util/sexpr/option_declarations.h"
#include "frontends/lean/util.h"
#include "library/protected.h"
#include "library/scoped_ext.h"
#include "util/bitap_fuzzy_search.h"
#include "library/type_context.h"
#include "kernel/instantiate.h"

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

class null_message_stream : public message_stream {
public:
    void report(message const &) override {}
};

server::server(unsigned num_threads, environment const & initial_env, io_state const & ios) :
        m_num_threads(num_threads), m_initial_env(initial_env), m_ios(ios) {
    m_ios.set_regular_channel(std::make_shared<stderr_channel>());
    m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());
    m_ios.set_message_channel(std::make_shared<null_message_stream>());
}

server::~server() {
}

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
    } else if (command == "show_goal") {
        return handle_show_goal(req);
    } else if (command == "info") {
        return handle_info(req);
    }

    json res;
    res["response"] = "error";
    res["message"] = "unknown command";
    return res;
}

static optional<pos_info> diff(std::string a, std::string b) {
    std::istringstream in_a(a), in_b(b);
    for (unsigned line = 1;; line++) {
        if (in_a.eof() && in_b.eof()) return optional<pos_info>();
        if (in_a.eof() || in_b.eof()) return optional<pos_info>(line, 0);

        std::string line_a, line_b;
        std::getline(in_a, line_a);
        std::getline(in_b, line_b);
        // TODO(gabriel): return column as well
        if (line_a != line_b) return optional<pos_info>(line, 0);
    }
}

json server::handle_sync(json const & req) {
    std::string new_file_name = req["file_name"];
    std::string new_content = req["content"];

    json res;
    res["response"] = "ok";

    if (m_file_name != new_file_name) {
        m_file_name = new_file_name;
        m_content = new_content;
        m_only_checked_until = optional<pos_info>(0, 0);
        res["message"] = "new file name, reloading";
    } else {
        if (auto diff_pos = diff(m_content, new_content)) {
            m_content = new_content;
            // TODO(gabriel): implement min on pos_info
            if (m_only_checked_until && m_only_checked_until->first < diff_pos->first) {
                // we have not yet checked up to the differing position
            } else {
                m_only_checked_until = diff_pos;
            }
            res["message"] = "file partially invalidated";
        } else {
            res["message"] = "no file changes";
        }
    }
    return res;
}

json server::handle_check(json const &) {
    try {
        if (imports_have_changed(m_checked_env))
            m_only_checked_until = optional<pos_info>(0, 0);
    } catch (...) {
        m_only_checked_until = optional<pos_info>(0, 0);
    }

    if (m_only_checked_until) {
        // keep all snapshots before the change but the last one (which may belong to the command that's being changed)
        auto it = m_snapshots.begin();
        while (it != m_snapshots.end() && it->m_pos < *m_only_checked_until)
            it++;
        if (it != m_snapshots.begin())
            it--;
        m_snapshots.erase(it, m_snapshots.end());

        std::istringstream in(m_content);
        bool use_exceptions = false;
        optional<std::string> base_dir;
        parser p(m_initial_env, m_ios, in, m_file_name.c_str(),
                 base_dir, use_exceptions, m_num_threads,
                 m_snapshots.empty() ? nullptr : &m_snapshots.back(),
                 &m_snapshots,
                 m_snapshots.empty() ? optional<info_manager>(info_manager()) : m_snapshots.back().m_infom);
        // TODO(gabriel): definition caches?

        m_parsed_ok = p();
        m_only_checked_until = optional<pos_info>();
        m_checked_env = p.env();
        m_messages = p.get_messages();
    }

    json res;
    res["response"] = "ok";
    res["is_ok"] = m_parsed_ok;
    std::list<json> json_messages;
    for_each(m_messages, [&](message const & msg) { json_messages.push_front(json_of_message(msg)); });
    res["messages"] = json_messages;
    return res;
}

snapshot const * server::get_closest_snapshot(unsigned line) {
    snapshot const * ret = m_snapshots.size() ? &m_snapshots.front() : nullptr;
    for (snapshot const & snap : m_snapshots) {
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

    if (!m_snapshots.size()) { // should only happen when imports have been touched
        handle_check({});
    }

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

json server::handle_show_goal(json const &req) {
    pos_info pos(req["line"], req["col"]);

    if (!m_snapshots.size()) handle_check({});

    snapshot * snap = nullptr;
    for (auto & s : m_snapshots) {
        if (s.m_pos.first < pos.first)
            snap = &s;
    }

    std::istringstream in(m_content);
    bool use_exceptions = false;
    optional<std::string> base_dir;
    parser p(m_initial_env, m_ios, in, m_file_name.c_str(),
             base_dir, use_exceptions, m_num_threads, snap);

    p.enable_show_goal(pos);

    try {
        p();
    } catch (show_goal_exception & ex) {
        json res;
        res["response"] = "ok";
        res["line"] = ex.m_pos.first;
        res["col"] = ex.m_pos.second;
        std::stringstream buf;
        buf << ex.m_state.pp();
        res["state"] = buf.str();
        return res;
    }

    json res;
    res["response"] = "error";
    res["message"] = "could not find goal";
    return res;
}

json server::handle_info(json const & req) {
    unsigned line = req["line"];
    optional<unsigned> col;
    if (req.count("col"))
        col = some<unsigned>(req["col"]);

    json res;
    res["response"] = "ok";
    res["messages"] = {};

    if (m_snapshots.size()) {
        auto const & snap = m_snapshots.back();
        assert(snap.m_infom);
        res["messages"] = snap.m_infom->get_messages(snap.m_env, snap.m_options, m_ios, line, col);
    }
    return res;
}

void initialize_server() {
    g_auto_completion_max_results = new name{"auto_completion", "max_results"};
    register_unsigned_option(*g_auto_completion_max_results, LEAN_DEFAULT_AUTO_COMPLETION_MAX_RESULTS,
                             "(auto-completion) maximum number of results returned");
}

void finalize_server() {
    delete g_auto_completion_max_results;
}
}
#endif
