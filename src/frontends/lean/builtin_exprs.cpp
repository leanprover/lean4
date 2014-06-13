/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parser.h"

namespace lean {
namespace notation {
static name g_llevel_curly(".{");
static name g_rcurly("}");

static expr parse_Type(parser & p, unsigned, expr const *) {
    if (p.curr_is_token(g_llevel_curly)) {
        p.next();
        level l = p.parse_level();
        p.check_token_next(g_rcurly, "invalid Type expression, '}' expected");
        return mk_sort(l);
    } else {
        return p.mk_Type();
    }
}

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
    r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    return r;
}

parse_table init_led_table() {
    parse_table r(false);
    r.add({transition("->", mk_expr_action(get_arrow_prec() + 1))}, mk_arrow(Var(0), Var(2)));
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
