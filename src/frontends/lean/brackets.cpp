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
#include "frontends/lean/structure_instance.h"

namespace lean {
/* Parse rest of the subtype expression prefix '{' id ':' expr '\\' ... */
static expr parse_subtype(parser & p, pos_info const & pos, expr const & local) {
    parser::local_scope scope(p);
    p.add_local(local);
    expr pred    = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid subtype, '}' expected");
    bool use_cache = false;
    pred         = p.save_pos(Fun(local, pred, use_cache), pos);
    expr subtype = p.save_pos(mk_constant(get_subtype_name()), pos);
    return p.mk_app(subtype, pred, pos);
}

/* Parse rest of the set_of expression prefix '{' id ':' expr '|' ... */
static expr parse_set_of(parser & p, pos_info const & pos, expr const & local) {
    parser::local_scope scope(p);
    p.add_local(local);
    expr pred    = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid set_of, '}' expected");
    bool use_cache = false;
    pred        = p.save_pos(Fun(local, pred, use_cache), pos);
    expr set_of = p.save_pos(mk_constant(get_set_of_name()), pos);
    return p.mk_app(set_of, pred, pos);
}

/* Create singletoncollection for '{' expr '}' */
static expr mk_singleton(parser & p, pos_info const & pos, expr const & e) {
    return p.mk_app(p.save_pos(mk_constant(get_singleton_name()), pos), e, pos);
}

/* Parse rest of the insertable '{' expr ... */
static expr parse_fin_set(parser & p, pos_info const & pos, expr const & e) {
    lean_assert(p.curr_is_token(get_comma_tk()) || p.curr_is_token(get_rcurly_tk()));
    expr r = mk_singleton(p, pos, e);
    while (p.curr_is_token(get_comma_tk())) {
        auto ins_pos = p.pos();
        p.next();
        if (p.curr_is_token(get_rcurly_tk())) break;
        expr e2 = p.parse_expr();
        expr insert = p.save_pos(mk_constant(get_has_insert_insert_name()), ins_pos);
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
    bool use_cache = false;
    pred   = p.rec_save_pos(Fun(local, pred, use_cache), pos);
    return p.rec_save_pos(mk_app(mk_constant(get_has_sep_sep_name()), pred, s), pos);
}

static expr parse_structure_instance_core(parser & p, optional<expr> const & src = {}, name const & S = {},
                                          buffer<name> fns = {}, buffer<expr> fvs = {}) {
    buffer<expr> sources;
    bool catchall = false;
    if (src)
        sources.push_back(*src);
    bool read_source = false;
    while (!p.curr_is_token(get_rcurly_tk())) {
        if (p.curr_is_token(get_dotdot_tk())) {
            p.next();
            if (p.curr_is_token(get_rcurly_tk())) {
                // ", ...}"
                catchall = true;
                break;
            }
            // ", ...src"
            sources.push_back(p.parse_expr());
            read_source = true;
        } else if (!read_source) {
            fns.push_back(p.check_id_next("invalid structure instance, identifier expected"));
            p.check_token_next(get_assign_tk(), "invalid structure instance, ':=' expected");
            fvs.push_back(p.parse_expr());
        } else {
            break;
        }
        // note: allows trailing ','
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
        } else {
            break;
        }
    }
    p.check_token_next(get_rcurly_tk(), "invalid structure instance, '}' expected");
    return mk_structure_instance(S, fns, fvs, sources, catchall);
}

/* Parse rest of the qualified structure instance prefix '{' S '.' ... */
static expr parse_qualified_structure_instance(parser & p, name S, pos_info const & S_pos) {
    S = p.to_constant(S, "invalid structure name", S_pos);
    return parse_structure_instance_core(p, none_expr(), S);
}

/* Parse rest of the structure instance prefix '{' fname ... */
static expr parse_structure_instance(parser & p, name const & fname) {
    buffer<name> fns;
    buffer<expr> fvs;
    fns.push_back(fname);
    p.check_token_next(get_assign_tk(), "invalid structure instance, ':=' expected");
    fvs.push_back(p.parse_expr());
    if (p.curr_is_token(get_comma_tk()))
        p.next();
    return parse_structure_instance_core(p, none_expr(), name(), fns, fvs);
}

static name * g_emptyc_or_emptys = nullptr;

bool is_emptyc_or_emptys(expr const & e) {
    return is_constant(e, *g_emptyc_or_emptys);
}

expr parse_curly_bracket(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e;
    if (p.curr_is_token(get_rcurly_tk())) {
        p.next();
        return p.save_pos(mk_constant(*g_emptyc_or_emptys), pos);
    } else if (p.curr_is_identifier()) {
        auto id_pos = p.pos();
        name id     = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_dslash_tk())) {
            expr type  = p.save_pos(mk_expr_placeholder(), id_pos);
            expr local = p.save_pos(mk_local(id, type), id_pos);
            p.next();
            return parse_subtype(p, pos, local);
        } else if (p.curr_is_token(get_bar_tk())) {
            expr type  = p.save_pos(mk_expr_placeholder(), id_pos);
            expr local = p.save_pos(mk_local(id, type), id_pos);
            p.next();
            return parse_set_of(p, pos, local);
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            expr type  = p.parse_expr();
            expr local = p.save_pos(mk_local(id, type), id_pos);
            if (p.curr_is_token(get_bar_tk())) {
                p.next();
                return parse_set_of(p, pos, local);
            } else {
                p.check_token_next(get_dslash_tk(), "invalid expression, '//' or '|' expected");
                return parse_subtype(p, pos, local);
            }
        } else if (p.curr_is_token(get_period_tk())) {
            p.next();
            return parse_qualified_structure_instance(p, id, id_pos);
        } else if (p.curr_is_token(get_assign_tk()) || p.curr_is_token(get_fieldarrow_tk())) {
            return parse_structure_instance(p, id);
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
    } else if (p.curr_is_token(get_period_tk())) {
        p.next();
        p.check_token_next(get_rcurly_tk(), "invalid empty structure instance, '}' expected");
        return p.save_pos(mk_structure_instance(), pos);
    } else if (p.curr_is_token(get_dotdot_tk())) {
        return parse_structure_instance_core(p);
    } else {
        e = p.parse_expr();
    }

    if (p.curr_is_token(get_comma_tk())) {
        return parse_fin_set(p, pos, e);
    } else if (p.curr_is_token(get_rcurly_tk())) {
        return parse_fin_set(p, pos, e);
    } else if (p.curr_is_token(get_with_tk())) {
        p.next();
        return parse_structure_instance_core(p, some_expr(e));
    } else {
        return p.parser_error_or_expr({"invalid '{' expression, ',', '}', '..', `//` or `|` expected", p.pos()});
    }
}

void initialize_brackets() {
    g_emptyc_or_emptys = new name("_emptyc_or_emptys");
}

void finalize_brackets() {
    delete g_emptyc_or_emptys;
}
}
