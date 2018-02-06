/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once

#include "util/message_definitions.h"
#include <string>
#include <vector>
#include "util/log_tree.h"
#include "util/task.h"
#include "frontends/lean/parser_state.h"
#include "frontends/lean/parser.h"

namespace lean {

pos_info find_end_pos(std::string const &);

struct module_parser_result {
    pos_range m_range;

    std::shared_ptr<snapshot const> m_snapshot_at_end;
    log_tree::node m_lt;

    cancellation_token m_cancel;
    task<module_parser_result> m_next;
};

task<module_parser_result> get_end(module_parser_result const &);

class module_parser : public std::enable_shared_from_this<module_parser> {
    std::istringstream m_in;
    parser m_parser;
    pos_info m_end_pos;

    bool m_separate_tasks = true;
    bool m_save_info = false;

    pair<cancellation_token, task<module_parser_result>>
    parse_next_command_like(optional<std::vector<gtask>> const & dependencies = {});

public:
    module_parser(std::string const & file_name, std::string const & content,
                  environment const & initial_env, module_loader const & import_fn);
    ~module_parser();

    void use_separate_tasks(bool separate_tasks) { m_separate_tasks = separate_tasks; }
    void save_info(bool save) { m_save_info = save; }
    void break_at_pos(pos_info const & pos, bool complete);

    pair<cancellation_token, task<module_parser_result>>
    resume(module_parser_result const &, optional<std::vector<gtask>> const & dependencies);

    module_parser_result resume_from_start(
        module_parser_result const &, cancellation_token const &,
        pos_info const & diff_pos,
        optional<std::vector<gtask>> const & dependencies,
        bool cancel_old = true);

    module_parser_result parse(optional<std::vector<gtask>> const & dependencies);
};

}
