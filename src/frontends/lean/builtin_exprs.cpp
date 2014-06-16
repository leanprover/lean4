/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/placeholder.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parser.h"

namespace lean {
namespace notation {
static name g_llevel_curly(".{");
static name g_rcurly("}");
static name g_in("in");
static name g_colon(":");
static name g_assign(":=");
static name g_comma(",");

static expr parse_Type(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.curr_is_token(g_llevel_curly)) {
        p.next();
        level l = p.parse_level();
        p.check_token_next(g_rcurly, "invalid Type expression, '}' expected");
        return p.save_pos(mk_sort(l), pos);
    } else {
        return p.save_pos(p.mk_Type(), pos);
    }
}

static expr parse_let(parser & p, pos_info const & pos);
static expr parse_let_body(parser & p, pos_info const & pos) {
    if (p.curr_is_token(g_comma)) {
        p.next();
        return parse_let(p, pos);
    } else if (p.curr_is_token(g_in)) {
        p.next();
        return p.parse_expr();
    } else {
        throw parser_error("invalid let declaration, 'in' or ',' expected", p.pos());
    }
}

static expr parse_let(parser & p, pos_info const & pos) {
    parser::local_scope scope1(p);
    if (p.parse_local_notation_decl()) {
        return parse_let_body(p, pos);
    } else {
        name id = p.check_id_next("invalid let declaration, identifier expected");
        expr type, value;
        if (p.curr_is_token(g_assign)) {
            p.next();
            type  = mk_expr_placeholder();
            value = p.parse_expr();
        } else if (p.curr_is_token(g_colon)) {
            p.next();
            type = p.parse_expr();
            p.check_token_next(g_assign, "invalid declaration, ':=' expected");
            value = p.parse_expr();
        } else {
            parser::local_scope scope2(p);
            buffer<parameter> ps;
            auto lenv = p.parse_binders(ps);
            if (p.curr_is_token(g_colon)) {
                p.next();
                type  = p.parse_scoped_expr(ps, lenv);
            } else {
                type  = mk_expr_placeholder();
            }
            p.check_token_next(g_assign, "invalid let declaration, ':=' expected");
            value = p.parse_scoped_expr(ps, lenv);
            type  = p.pi_abstract(ps, type);
            value = p.lambda_abstract(ps, value);
        }
        expr l = mk_local(id, id, type);
        p.add_local(l);
        expr body = abstract(parse_let_body(p, pos), l);
        return p.save_pos(mk_let(id, type, value, body), pos);
    }
}

static expr parse_let_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_let(p, pos);
}

static expr parse_placeholder(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_expr_placeholder(), pos);
}

static expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    tactic t = p.parse_tactic();
    expr r = p.save_pos(mk_expr_placeholder(), pos);
    p.save_hint(r, t);
    return r;
}

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("_", mk_ext_action(parse_placeholder))}, x0);
    r = r.add({transition("by", mk_ext_action(parse_by))}, x0);
    r = r.add({transition("(", Expr), transition(")", Skip)}, x0);
    r = r.add({transition("fun", Binders), transition(",", mk_scoped_expr_action(x0))}, x0);
    r = r.add({transition("Pi", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    r = r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    r = r.add({transition("let", mk_ext_action(parse_let_expr))}, x0);
    return r;
}

parse_table init_led_table() {
    parse_table r(false);
    r = r.add({transition("->", mk_expr_action(get_arrow_prec()-1))}, mk_arrow(Var(1), Var(1)));
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
