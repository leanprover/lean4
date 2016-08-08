/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "library/placeholder.h"
#include "library/definitional/equations.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"

namespace lean {
static name * g_match_name = nullptr;

bool is_match_binder_name(name const & n) { return n == *g_match_name; }

/** \brief Use equations compiler infrastructure to implement match-with */
expr parse_match(parser & p, unsigned, expr const *, pos_info const & pos) {
    parser::local_scope scope(p);
    buffer<expr> eqns;
    expr t;
    try {
        t  = p.parse_expr();
        p.check_token_next(get_with_tk(), "invalid 'match' expression, 'with' expected");
        expr fn = mk_local(mk_fresh_name(), *g_match_name, mk_expr_placeholder(), binder_info());
        if (p.curr_is_token(get_end_tk())) {
            p.next();
            // empty match-with
            eqns.push_back(Fun(fn, mk_no_equation()));
            expr f = p.save_pos(mk_equations(1, eqns.size(), eqns.data()), pos);
            return p.mk_app(f, t, pos);
        }
        if (is_eqn_prefix(p))
            p.next(); // optional '|' in the first case
        while (true) {
            buffer<expr> locals;
            auto lhs_pos = p.pos();
            expr lhs = p.parse_pattern(locals);
            lhs = p.mk_app(fn, lhs, lhs_pos);
            auto assign_pos = p.pos();
            p.check_token_next(get_assign_tk(), "invalid 'match' expression, ':=' expected");
            {
                parser::local_scope scope2(p);
                for (expr const & local : locals)
                    p.add_local(local);
                expr rhs = p.parse_expr();
                eqns.push_back(Fun(fn, Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p)));
            }
            if (!is_eqn_prefix(p))
                break;
            p.next();
        }
    } catch (exception & ex) {
        consume_until_end(p);
        ex.rethrow();
    }
    p.check_token_next(get_end_tk(), "invalid 'match' expression, 'end' expected");
    expr f = p.save_pos(mk_equations(1, eqns.size(), eqns.data()), pos);
    return p.mk_app(f, t, pos);
}

void initialize_match_expr() {
    g_match_name = new name("_match");
}

void finalize_match_expr() {
    delete g_match_name;
}
}
