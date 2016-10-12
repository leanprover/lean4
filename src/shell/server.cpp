/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/

#include "frontends/lean/parser.h"
#include "shell/server.h"
#include <list>

namespace lean {

class null_message_stream : public message_stream {
public:
    void report(message const &) override {}
};

server::server(optional<std::string> const & base_dir, int num_threads, environment const & initial_env, io_state const & ios) :
        m_base_dir(base_dir), m_num_threads(num_threads),
        m_initial_env(initial_env), m_ios(ios) {
    m_ios.set_regular_channel(std::make_shared<stderr_channel>());
    m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());
    m_ios.set_message_channel(std::make_shared<null_message_stream>());
}

server::~server() {
}

void server::run() {
    scope_global_ios scoped_ios(m_ios);

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
        m_only_checked_until = optional<pos_info>(1, 0);
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
    if (m_only_checked_until) {
        snapshot_vector new_snapshots;
        for (snapshot const & snap : m_snapshots) {
            if (snap.m_pos.first < m_only_checked_until->first) {
                new_snapshots.push_back(snap);
            } else {
                break;
            }
        }

        std::istringstream in(m_content);
        bool use_exceptions = false;
        parser p(m_initial_env, m_ios, in, m_file_name.c_str(),
                 m_base_dir, use_exceptions, m_num_threads,
                 new_snapshots.empty() ? nullptr : &new_snapshots.back(),
                 &new_snapshots);
        // TODO(gabriel): definition caches?

        m_parsed_ok = p();
        m_only_checked_until = optional<pos_info>();
        m_checked_env = p.env();
        m_messages = p.get_messages();
        m_snapshots = new_snapshots;
    }

    json res;
    res["response"] = "ok";
    res["is_ok"] = m_parsed_ok;
    std::list<json> json_messages;
    for_each(m_messages, [&](message const & msg) { json_messages.push_front(json_of_message(msg)); });
    res["messages"] = json_messages;
    return res;
}

}
