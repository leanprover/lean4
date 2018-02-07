/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "library/placeholder.h"
#include "library/equations_compiler/equations.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_util.h"

namespace lean {
static name * g_match_name = nullptr;

bool is_match_binder_name(name const & n) { return n == *g_match_name; }

/** \brief Use equations compiler infrastructure to implement match-with */
expr parse_match(parser & p, unsigned, expr const *, pos_info const & pos) {
    parser::local_scope scope1(p);
    match_definition_scope scope2(p.env());
    equations_header header = mk_match_header(scope2.get_name(), scope2.get_actual_name());
    buffer<expr> eqns;
    buffer<expr> ts;
    try {
        ts.push_back(p.parse_expr());
        while (p.curr_is_token(get_comma_tk())) {
            p.next();
            ts.push_back(p.parse_expr());
        }
        expr fn;
        /* Parse optional type */
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            expr type = p.parse_expr();
            fn = mk_local(p.next_name(), *g_match_name, type, mk_rec_info(true));
        } else {
            fn = mk_local(p.next_name(), *g_match_name, mk_expr_placeholder(), mk_rec_info(true));
        }

        p.check_token_next(get_with_tk(), "invalid 'match' expression, 'with' expected");

        if (p.curr_is_token(get_end_tk())) {
            /* Empty match */
            p.next();
            eqns.push_back(Fun(fn, mk_no_equation()));
            expr f = p.save_pos(mk_equations(header, eqns.size(), eqns.data()), pos);
            return p.mk_app(f, ts, pos);
        }
        if (is_eqn_prefix(p))
            p.next(); // optional '|' in the first case
        while (true) {
            auto lhs_pos = p.pos();
            buffer<expr> lhs_args;
            lhs_args.push_back(p.parse_pattern_or_expr());
            while (p.curr_is_token(get_comma_tk())) {
                p.next();
                lhs_args.push_back(p.parse_pattern_or_expr());
            }
            expr lhs = p.mk_app(fn, lhs_args, lhs_pos);
            buffer<expr> locals;
            bool skip_main_fn = true;
            lhs = p.patexpr_to_pattern(lhs, skip_main_fn, locals);
            auto assign_pos = p.pos();
            p.check_token_next(get_assign_tk(), "invalid 'match' expression, ':=' expected");
            {
                parser::local_scope scope2(p);
                for (expr const & local : locals)
                    p.add_local(local);
                expr rhs = p.parse_expr();
                eqns.push_back(Fun(fn, Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p), p));
            }
            if (!is_eqn_prefix(p))
                break;
            p.next();
        }
    } catch (exception & ex) {
        consume_until_end_or_command(p);
        ex.rethrow();
    }
    p.check_token_next(get_end_tk(), "invalid 'match' expression, 'end' expected");
    expr f = p.save_pos(mk_equations(header, eqns.size(), eqns.data()), pos);
    return p.mk_app(f, ts, pos);
}

void initialize_match_expr() {
    g_match_name = new name("_match");
}

void finalize_match_expr() {
    delete g_match_name;
}
}
