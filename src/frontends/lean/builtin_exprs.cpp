/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/builtin_exprs.h"

namespace lean {
namespace notation {

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_var(0);
    parse_table r;
    r.add({transition("Bool", Skip)}, Bool);
    r.add({transition("(", Expr), transition(")", Skip)}, x0);
    r.add({transition("fun", Binders), transition(",", mk_scoped_expr_action(x0))}, x0);
    r.add({transition("Pi", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    return r;
}

parse_table init_led_table() {
    parse_table r;
    // TODO(Leo)
    return r;
}
}

parse_table get_builtin_nud_table() {
    static optional<parse_table> r;
    if (!r)
        r = notation::init_nud_table();
    return *r;
}

parse_table get_builtin_led_table() {
    static optional<parse_table> r;
    if (!r)
        r = notation::init_led_table();
    return *r;
}
}
