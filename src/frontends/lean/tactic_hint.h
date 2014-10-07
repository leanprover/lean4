/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
list<expr> const & get_tactic_hints(environment const & env);
class parser;
expr parse_tactic_name(parser & p);
void register_tactic_hint_cmd(cmd_table & r);

void initialize_tactic_hint();
void finalize_tactic_hint();
}
