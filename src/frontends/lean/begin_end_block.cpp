/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/quote.h"
#include "library/placeholder.h"
#include "library/tactic/elaborate.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"

namespace lean {
static name * g_begin_end = nullptr;
static name * g_begin_end_element = nullptr;

static expr mk_begin_end_block(expr const & e) { return mk_annotation(*g_begin_end, e, nulltag); }
bool is_begin_end_block(expr const & e) { return is_annotation(e, *g_begin_end); }

static expr mk_begin_end_element(expr const & e) { return mk_annotation(*g_begin_end_element, e, nulltag); }
static bool is_begin_end_element(expr const & e) { return is_annotation(e, *g_begin_end_element); }

static expr mk_begin_end_element(parser & p, expr tac, pos_info const & pos) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    tac = p.save_pos(mk_app(mk_constant(get_tactic_step_name()), tac), pos);
    return p.save_pos(mk_begin_end_element(tac), pos);
}

static expr concat(parser & p, expr const & r, expr tac, pos_info const & start_pos, pos_info const & pos) {
    tac = mk_begin_end_element(p, tac, pos);
    return p.save_pos(mk_app(mk_constant(get_monad_and_then_name()), r, tac), start_pos);
}

void get_begin_end_block_elements(expr const & e, buffer<expr> & elems) {
    lean_assert(is_begin_end_block(e));
    if (is_app(e)) {
        get_begin_end_block_elements(app_fn(e), elems);
        get_begin_end_block_elements(app_arg(e), elems);
    } else if (is_begin_end_element(e)) {
        elems.push_back(get_annotation_arg(e));
    } else {
        /* do nothing */
    }
}

static optional<name> is_tactic_interactive(parser & p) {
    if (!p.curr_is_identifier()) return optional<name>();
    name id = get_tactic_interactive_name() + p.get_name_val();
    if (p.env().find(id))
        return optional<name>(id);
    else
        return optional<name>();
}

static expr parse_auto_quoted_expr(parser & p, unsigned rbp) {
    auto pos = p.pos();
    parser::quote_scope scope(p, true);
    expr e = p.parse_expr(rbp);
    return p.save_pos(mk_quote(e), pos);
}

static expr parse_tactic_interactive(parser & p, name const & decl_name) {
    auto pos = p.pos();
    p.next();
    expr type = p.env().get(decl_name).get_type();
    unsigned arity = get_arity(type);
    buffer<expr> args;
    while (is_pi(type)) {
        if (is_explicit(binding_info(type))) {
            expr arg_type = binding_domain(type);
            if (is_constant(arg_type, get_pexpr_name())) {
                /* auto quote expressions */
                expr arg = parse_auto_quoted_expr(p, arity == 1 ? 0 : get_max_prec());
                args.push_back(arg);
            } else if (is_constant(arg_type, get_name_name())) {
                if (!p.curr_is_identifier())
                    throw parser_error(sstream() << "invalid tactic '" << decl_name  << "', identifier expected", p.pos());
                name id = p.get_name_val();
                p.next();
                args.push_back(quote_name(id));
            } else {
                args.push_back(p.parse_expr(get_max_prec()));
            }
        }
        type = binding_body(type);
    }
    return p.rec_save_pos(mk_app(mk_constant(decl_name), args), pos);
}

expr parse_begin_end_core(parser & p, pos_info const & start_pos,
                          name const & end_token, bool nested = false) {
    p.next();
    bool first = true;
    expr r = mk_begin_end_element(p, mk_constant(get_tactic_skip_name()), start_pos);
    try {
        while (!p.curr_is_token(end_token)) {
            auto pos = p.pos();
            if (first) {
                first = false;
            } else {
                p.check_token_next(get_comma_tk(), "invalid 'begin-end' expression, ',' expected");
            }
            /* parse next element */
            expr next_tac;
            if (p.curr_is_token(get_begin_tk())) {
                next_tac = parse_begin_end_core(p, pos, get_end_tk(), true);
            } else if (p.curr_is_token(get_lcurly_tk())) {
                next_tac = parse_begin_end_core(p, pos, get_rcurly_tk(), true);
            } else if (p.curr_is_token(end_token)) {
                break;
            } else if (auto dname = is_tactic_interactive(p)) {
                next_tac = parse_tactic_interactive(p, *dname);
            } else {
                next_tac = p.parse_expr();
            }
            r = concat(p, r, next_tac, start_pos, pos);
        }
    } catch (exception & ex) {
        if (end_token == get_end_tk())
            consume_until_end(p);
        throw;
    }
    auto end_pos = p.pos();
    p.next();
    r = p.save_pos(mk_begin_end_block(r), end_pos);
    if (nested)
        return r;
    else
        return p.save_pos(mk_by(r), end_pos);
}

expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_begin_end_core(p, pos, get_end_tk());
}

void initialize_begin_end_block() {
    g_begin_end  = new name("begin_end");
    register_annotation(*g_begin_end);

    g_begin_end_element = new name("begin_end_element");
    register_annotation(*g_begin_end_element);
}

void finalize_begin_end_block() {
    delete g_begin_end;
    delete g_begin_end_element;
}
}
