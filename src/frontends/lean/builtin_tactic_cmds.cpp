/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_bang("!");

tactic parse_fail_tactic(parser &) { return fail_tactic(); }
tactic parse_id_tactic(parser &) { return id_tactic(); }
tactic parse_now_tactic(parser &) { return now_tactic(); }
tactic parse_show_tactic(parser &) { return trace_state_tactic(); }
tactic parse_assumption_tactic(parser &) { return assumption_tactic(); }

tactic parse_unfold_tactic(parser & p) {
    auto pos = p.pos();
    expr id  = p.parse_expr();
    if (!is_constant(id))
        throw parser_error("invalid 'unfold' tactic, constant expected", pos);
    return unfold_tactic(const_name(id));
}

tactic parse_repeat_tactic(parser & p) {
    tactic t = p.parse_tactic();
    if (p.curr_is_numeral()) {
        unsigned n = p.parse_small_nat();
        return repeat_at_most(t, n);
    } else {
        return repeat(t);
    }
}

tactic parse_echo_tactic(parser & p) {
    if (!p.curr_is_string())
        throw parser_error("invalid 'echo' tactic, string expected", p.pos());
    tactic r = trace_tactic(p.get_str_val());
    p.next();
    return r;
}

void add_tactic(tactic_cmd_table & t, tactic_cmd_info && info) { t.insert(info.get_name(), info); }

tactic_cmd_table get_builtin_tactic_cmds() {
    tactic_cmd_table t;
    add_tactic(t, tactic_cmd_info("fail", "always fail tactic", parse_fail_tactic));
    add_tactic(t, tactic_cmd_info("show", "show goals tactic", parse_show_tactic));
    add_tactic(t, tactic_cmd_info("now",  "succeeds only if all goals have been solved", parse_now_tactic));
    add_tactic(t, tactic_cmd_info("echo", "trace tactic: display message", parse_echo_tactic));
    add_tactic(t, tactic_cmd_info("unfold", "unfold definition", parse_unfold_tactic));
    add_tactic(t, tactic_cmd_info("repeat", "repeat tactic", parse_repeat_tactic));
    add_tactic(t, tactic_cmd_info("!", "repeat tactic", parse_repeat_tactic));
    add_tactic(t, tactic_cmd_info("id", "do nothing tactic", parse_id_tactic));
    add_tactic(t, tactic_cmd_info("assumption", "solve goal if there is an assumption that is identical to the conclusion",
                                  parse_assumption_tactic));
    add_tactic(t, tactic_cmd_info("exact", "solve goal if there is an assumption that is identical to the conclusion",
                                  parse_assumption_tactic));
    return t;
}
}
