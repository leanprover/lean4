/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/placeholder.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
/* Parse rest of the subtype expression prefix '{' id ':' expr '\\' ... */
static expr parse_subtype(parser & p, pos_info const & pos, expr const & local) {
    parser::local_scope scope(p);
    p.add_local(local);
    expr pred    = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid subtype, '}' expected");
    pred         = p.save_pos(Fun(local, pred), pos);
    expr subtype = p.save_pos(mk_constant(get_subtype_name()), pos);
    return p.mk_app(subtype, pred, pos);
}

/* Create empty collection for '{' '}' */
static expr mk_empty_collection(parser & p, pos_info const & pos) {
    return p.save_pos(mk_constant(get_empty_col_name()), pos);
}

/* Create singletoncollection for '{' expr '}' */
static expr mk_singleton(parser & p, pos_info const & pos, expr const & e) {
    return p.mk_app(p.save_pos(mk_constant(get_singleton_name()), pos), e, pos);
}

/* Parse rest of the insertable '{' expr ... */
static expr parse_insertable(parser & p, pos_info const & pos, expr const & e) {
    lean_assert(p.curr_is_token(get_comma_tk()));
    expr r = mk_singleton(p, pos, e);
    while (p.curr_is_token(get_comma_tk())) {
        auto ins_pos = p.pos();
        p.next();
        expr e2 = p.parse_expr();
        expr insert = p.save_pos(mk_constant(get_insert_name()), ins_pos);
        r = p.rec_save_pos(mk_app(insert, e2, r), ins_pos);
    }
    p.check_token_next(get_rcurly_tk(), "invalid explicit finite collection, '}' expected");
    return r;
}

/* Parse rest of the sep expression '{' id '∈' ... */
static expr parse_sep(parser & p, pos_info const & pos, name const & id) {
    expr s = p.parse_expr();
    p.check_token_next(get_bar_tk(), "invalid sep expression, '|' expected");
    parser::local_scope scope(p);
    expr local = p.save_pos(mk_local(id, p.save_pos(mk_expr_placeholder(), pos)), pos);
    p.add_local(local);
    expr pred  = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid sep expression, '}' expected");
    pred   = Fun(local, pred);
    return p.rec_save_pos(mk_app(mk_constant(get_sep_name()), pred, s), pos);
}

/* Parse rest of the monadic comprehension expression '{' expr '|' ... */
static expr parse_monadic_comprehension(parser & p, pos_info const & pos, expr const & e) {
    throw parser_error("monadic comprehension was not implemented yet", pos);
}

/* Parse rest of the qualified structure instance prefix '{' S '.' ... */
static expr parse_qualified_structure_instance(parser & p, pos_info const & pos, name const & S) {
    throw parser_error("qualified strucuture instance was not implemented yet", pos);
}

/* Parse rest of the structure instance prefix '{' fname ... */
static expr parse_structure_instance(parser & p, pos_info const & pos, name const & fname) {
    throw parser_error("strucuture instance was not implemented yet", pos);
}

/* Parse rest of the structure instance update '{' expr 'with' ... */
static expr parse_structure_instance_update(parser & p, pos_info const & pos, expr const & e) {
    throw parser_error("strucuture instance update was not implemented yet", pos);
}

expr parse_curly_bracket(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e;
    if (p.curr_is_token(get_rcurly_tk())) {
        p.next();
        return mk_empty_collection(p, pos);
    } else if (p.curr_is_identifier()) {
        auto id_pos = p.pos();
        name id     = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_dslash_tk())) {
            expr type  = p.save_pos(mk_expr_placeholder(), id_pos);
            expr local = p.save_pos(mk_local(id, type), id_pos);
            p.next();
            return parse_subtype(p, pos, local);
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            expr type  = p.parse_expr();
            expr local = p.save_pos(mk_local(id, type), id_pos);
            p.check_token_next(get_dslash_tk(), "invalid subtype, '//' expected");
            return parse_subtype(p, pos, local);
        } else if (p.curr_is_token(get_period_tk())) {
            p.next();
            return parse_qualified_structure_instance(p, pos, id);
        } else if (p.curr_is_token(get_assign_tk()) || p.curr_is_token(get_fieldarrow_tk())) {
            return parse_structure_instance(p, pos, id);
        } else if (p.curr_is_token(get_membership_tk()) || p.curr_is_token(get_in_tk())) {
            p.next();
            return parse_sep(p, pos, id);
        } else {
            expr left = p.id_to_expr(id, id_pos);
            unsigned rbp = 0;
            while (rbp < p.curr_lbp()) {
                left = p.parse_led(left);
            }
            e = left;
        }
    } else {
        e = p.parse_expr();
    }

    if (p.curr_is_token(get_comma_tk())) {
        return parse_insertable(p, pos, e);
    } else if (p.curr_is_token(get_rcurly_tk())) {
        return parse_insertable(p, pos, e);
    } else if (p.curr_is_token(get_with_tk())) {
        p.next();
        return parse_structure_instance_update(p, pos, e);
    } else if (p.curr_is_token(get_bar_tk())) {
        p.next();
        return parse_monadic_comprehension(p, pos, e);
    } else {
        throw parser_error("invalid '{' expression, ',', '}', 'with', `//` or `|` expected", p.pos());
    }
}
}
