/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic.h"
#include "frontends/lean/parser.h"

namespace lean {
tactic parse_fail_tactic(parser &) { return fail_tactic(); }
tactic parse_id_tactic(parser &) { return id_tactic(); }
tactic parse_assumption_tactic(parser &) { return assumption_tactic(); }

void add_tactic(tactic_cmd_table & t, tactic_cmd_info && info) { t.insert(info.get_name(), info); }

tactic_cmd_table get_builtin_tactic_cmds() {
    tactic_cmd_table t;
    add_tactic(t, tactic_cmd_info("fail", "always fail tactic", parse_fail_tactic));
    add_tactic(t, tactic_cmd_info("id", "do nothing tactic", parse_id_tactic));
    add_tactic(t, tactic_cmd_info("assumption", "solve goal if there is an assumption that is identical to the conclusion",
                                  parse_assumption_tactic));
    add_tactic(t, tactic_cmd_info("exact", "solve goal if there is an assumption that is identical to the conclusion",
                                  parse_assumption_tactic));
    return t;
}
}
