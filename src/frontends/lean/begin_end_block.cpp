/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/annotation.h"
#include "library/constants.h"
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
    tac = p.save_pos(mk_app(mk_constant(get_tactic_consume_name()), tac), pos);
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
            if (p.curr_is_token(get_begin_tk())) {
                r = concat(p, r, parse_begin_end_core(p, pos, get_end_tk(), true), start_pos, pos);
            } else if (p.curr_is_token(get_lcurly_tk())) {
                r = concat(p, r, parse_begin_end_core(p, pos, get_rcurly_tk(), true), start_pos, pos);
            } else if (p.curr_is_token(end_token)) {
                break;
            } else {
                expr tac = p.parse_expr();
                r = concat(p, r, tac, start_pos, pos);
            }
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
