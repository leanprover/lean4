/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
class tactic_hint_entry {
    friend struct tactic_hint_config;
    expr   m_pre_tactic;
    tactic m_tactic;
    bool   m_compiled;
public:
    tactic_hint_entry():m_compiled(false) {}
    tactic_hint_entry(expr const & pre_tac, tactic const & tac):
        m_pre_tactic(pre_tac), m_tactic(tac), m_compiled(true) {}
    expr const & get_pre_tactic() const { return m_pre_tactic; }
    tactic const & get_tactic() const { return m_tactic; }
};
list<tactic_hint_entry> get_tactic_hints(environment const & env);
class parser;
expr parse_tactic_name(parser & p);
void register_tactic_hint_cmd(cmd_table & r);

void initialize_tactic_hint();
void finalize_tactic_hint();
}
