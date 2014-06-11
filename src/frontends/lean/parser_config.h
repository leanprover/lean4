/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
struct parser_config {
    token_table      m_tokens;
    parse_table      m_nud;
    parse_table      m_led;
    cmd_table        m_cmds;
    tactic_cmd_table m_tactic_cmds;
    parser_config();
};

parser_config const & get_parser_config(environment const & env);
environment update_parser_config(environment const & env, parser_config const & c);
}
