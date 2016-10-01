/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/quote.h"
#include "library/typed_expr.h"
#include "library/placeholder.h"
#include "library/tactic/elaborate.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tactic_notation.h"

namespace lean {
static name * g_begin_end = nullptr;
static name * g_begin_end_element = nullptr;

static expr mk_begin_end_block(expr const & e) { return mk_annotation(*g_begin_end, e, nulltag); }
bool is_begin_end_block(expr const & e) { return is_annotation(e, *g_begin_end); }

static expr mk_begin_end_element(expr const & e) { return mk_annotation(*g_begin_end_element, e, nulltag); }
bool is_begin_end_element(expr const & e) { return is_annotation(e, *g_begin_end_element); }

static expr mk_begin_end_element(parser & p, expr tac, pos_info const & pos) {
    if (is_begin_end_block(tac)) {
        return tac;
    } else {
        if (tac.get_tag() == nulltag)
            tac = p.save_pos(tac, pos);
        tac = p.save_pos(mk_app(mk_constant(get_tactic_step_name()), tac), pos);
        return p.save_pos(mk_begin_end_element(tac), pos);
    }
}

static expr concat(parser & p, expr const & r, expr tac, pos_info const & start_pos, pos_info const & pos) {
    tac = mk_begin_end_element(p, tac, pos);
    return p.save_pos(mk_app(mk_constant(get_monad_and_then_name()), r, tac), start_pos);
}

static void get_begin_end_block_elements_core(expr const & e, buffer<expr> & elems) {
    if (is_app(e)) {
        get_begin_end_block_elements_core(app_fn(e), elems);
        get_begin_end_block_elements_core(app_arg(e), elems);
    } else if (is_begin_end_element(e)) {
        elems.push_back(e);
    } else if (is_begin_end_block(e)) {
        /* Nested block */
        elems.push_back(e);
    } else {
        /* do nothing */
    }
}

void get_begin_end_block_elements(expr const & e, buffer<expr> & elems) {
    lean_assert(is_begin_end_block(e));
    return get_begin_end_block_elements_core(get_annotation_arg(e), elems);
}

static optional<name> is_auto_quote_tactic(parser & p) {
    if (!p.curr_is_identifier()) return optional<name>();
    name id = get_tactic_interactive_name() + p.get_name_val();
    if (p.env().find(id))
        return optional<name>(id);
    else
        return optional<name>();
}

static expr mk_lean_list(buffer<expr> const & es) {
    expr r = mk_constant(get_list_nil_name());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = mk_app(mk_constant(get_list_cons_name()), es[i], r);
    }
    return r;
}

static expr mk_lean_none() {
    return mk_constant(get_option_none_name());
}

static expr mk_lean_some(expr const & e) {
    return mk_app(mk_constant(get_option_some_name()), e);
}

static expr parse_quoted_ident(parser & p, name const & decl_name) {
    if (!p.curr_is_identifier())
        throw parser_error(sstream() << "invalid auto-quote tactic '" << decl_name  << "', identifier expected", p.pos());
    auto pos = p.pos();
    name id  = p.get_name_val();
    p.next();
    return p.save_pos(quote_name(id), pos);
}

static expr parse_optional_quoted_ident(parser & p, name const & decl_name) {
    auto pos = p.pos();
    if (p.curr_is_identifier())
        return p.save_pos(mk_lean_some(parse_quoted_ident(p, decl_name)), pos);
    else
        return p.save_pos(mk_lean_none(), pos);
}


static expr parse_using_id(parser & p, name const & decl_name) {
    auto pos = p.pos();
    if (p.curr_is_token(get_using_tk())) {
        p.next();
        return p.save_pos(mk_lean_some(parse_quoted_ident(p, decl_name)), pos);
    } else {
        return p.save_pos(mk_lean_none(), pos);
    }
}

static expr parse_qexpr(parser & p, unsigned rbp) {
    auto pos = p.pos();
    parser::quote_scope scope(p, true);
    expr e = p.parse_expr(rbp);
    return p.save_pos(mk_quote(e), pos);
}

static expr parse_qexpr_list(parser & p) {
    buffer<expr> result;
    auto pos = p.pos();
    p.check_token_next(get_lbracket_tk(), "invalid auto-quote tactic argument, '[' expected");
    while (!p.curr_is_token(get_rbracket_tk())) {
        result.push_back(parse_qexpr(p, 0));
        if (!p.curr_is_token(get_comma_tk())) break;
        p.next();
    }
    p.check_token_next(get_rbracket_tk(), "invalid auto-quote tactic argument, ']' expected");
    return p.rec_save_pos(mk_lean_list(result), pos);
}

static expr parse_opt_qexpr_list(parser & p) {
    if (p.curr_is_token(get_lbracket_tk()))
        return parse_qexpr_list(p);
    else
        return mk_constant(get_list_nil_name());
}

static expr parse_qexpr_list_or_qexpr0(parser & p) {
    if (p.curr_is_token(get_lbracket_tk())) {
        return parse_qexpr_list(p);
    } else {
        auto pos = p.pos();
        buffer<expr> args;
        args.push_back(parse_qexpr(p, 0));
        return p.rec_save_pos(mk_lean_list(args), pos);
    }
}

static expr parse_raw_id_list(parser & p) {
    auto pos = p.pos();
    buffer<expr> result;
    while (p.curr_is_identifier()) {
        auto id_pos = p.pos();
        name id = p.get_name_val();
        p.next();
        result.push_back(p.save_pos(quote_name(id), id_pos));
    }
    return p.rec_save_pos(mk_lean_list(result), pos);
}

static expr parse_with_id_list(parser & p) {
    if (p.curr_is_token(get_with_tk())) {
        p.next();
        return parse_raw_id_list(p);
    } else {
        return p.save_pos(mk_constant(get_list_nil_name()), p.pos());
    }
}

static expr parse_without_id_list(parser & p) {
    if (p.curr_is_token(get_without_tk())) {
        p.next();
        return parse_raw_id_list(p);
    } else {
        return p.save_pos(mk_constant(get_list_nil_name()), p.pos());
    }
}

static expr parse_location(parser & p) {
    if (p.curr_is_token(get_at_tk())) {
        p.next();
        return parse_raw_id_list(p);
    } else {
        return p.save_pos(mk_constant(get_list_nil_name()), p.pos());
    }
}

static expr parse_nested_auto_quote_tactic(parser & p) {
    auto pos = p.pos();
    bool nested = true;
    if (p.curr_is_token(get_lcurly_tk())) {
        return parse_begin_end_core(p, pos, get_rcurly_tk(), nested);
    } else if (p.curr_is_token(get_begin_tk())) {
        return parse_begin_end_core(p, pos, get_end_tk(), nested);
    } else {
        throw parser_error("invalid nested auto-quote tactic, '{' or 'begin' expected", pos);
    }
}

static expr parse_auto_quote_tactic(parser & p, name const & decl_name) {
    auto pos = p.pos();
    p.next();
    expr type = p.env().get(decl_name).get_type();
    buffer<expr> args;
    while (is_pi(type)) {
        if (is_explicit(binding_info(type))) {
            expr arg_type = binding_domain(type);
            if (is_constant(arg_type, get_tactic_interactive_types_qexpr_name())) {
                args.push_back(parse_qexpr(p, get_max_prec()));
            } else if (is_constant(arg_type, get_tactic_interactive_types_qexpr0_name())) {
                args.push_back(parse_qexpr(p, 0));
            } else if (is_constant(arg_type, get_tactic_interactive_types_qexpr_list_name())) {
                args.push_back(parse_qexpr_list(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_opt_qexpr_list_name())) {
                args.push_back(parse_opt_qexpr_list(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_qexpr_list_or_qexpr0_name())) {
                args.push_back(parse_qexpr_list_or_qexpr0(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_ident_name())) {
                args.push_back(parse_quoted_ident(p, decl_name));
            } else if (is_constant(arg_type, get_tactic_interactive_types_opt_ident_name())) {
                args.push_back(parse_optional_quoted_ident(p, decl_name));
            } else if (is_constant(arg_type, get_tactic_interactive_types_raw_ident_list_name())) {
                args.push_back(parse_raw_id_list(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_with_ident_list_name())) {
                args.push_back(parse_with_id_list(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_without_ident_list_name())) {
                args.push_back(parse_without_id_list(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_using_ident_name())) {
                args.push_back(parse_using_id(p, decl_name));
            } else if (is_constant(arg_type, get_tactic_interactive_types_location_name())) {
                args.push_back(parse_location(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_itactic_name())) {
                args.push_back(parse_nested_auto_quote_tactic(p));
            } else if (is_constant(arg_type, get_tactic_interactive_types_colon_tk_name())) {
                p.check_token_next(get_colon_tk(), "invalid auto-quote tactic, ':' expected");
                args.push_back(mk_constant(get_unit_star_name()));
            } else if (is_constant(arg_type, get_tactic_interactive_types_assign_tk_name())) {
                p.check_token_next(get_assign_tk(), "invalid auto-quote tactic, ':=' expected");
                args.push_back(mk_constant(get_unit_star_name()));
            } else if (is_constant(arg_type, get_tactic_interactive_types_comma_tk_name())) {
                p.check_token_next(get_comma_tk(), "invalid auto-quote tactic, ',' expected");
                args.push_back(mk_constant(get_unit_star_name()));
            } else {
                args.push_back(p.parse_expr(get_max_prec()));
            }
        }
        type = binding_body(type);
    }
    return p.rec_save_pos(mk_app(mk_constant(decl_name), args), pos);
}

static expr parse_tactic(parser & p) {
    if (auto dname = is_auto_quote_tactic(p)) {
        return parse_auto_quote_tactic(p, *dname);
    } else {
        return p.parse_expr();
    }
}

expr parse_begin_end_core(parser & p, pos_info const & start_pos,
                          name const & end_token, bool nested) {
    p.next();
    bool first = true;
    expr r = mk_begin_end_element(p, mk_constant(get_tactic_skip_name()), start_pos);
    try {
        while (!p.curr_is_token(end_token)) {
            if (first) {
                first = false;
            } else {
                p.check_token_next(get_comma_tk(), "invalid 'begin-end' expression, ',' expected");
            }
            auto pos = p.pos();
            /* parse next element */
            expr next_tac;
            if (p.curr_is_token(get_begin_tk())) {
                next_tac = parse_begin_end_core(p, pos, get_end_tk(), true);
            } else if (p.curr_is_token(get_lcurly_tk())) {
                next_tac = parse_begin_end_core(p, pos, get_rcurly_tk(), true);
            } else if (p.curr_is_token(get_do_tk())) {
                expr tac  = p.parse_expr();
                expr type = mk_tactic_unit();
                next_tac  = p.rec_save_pos(mk_typed_expr(type, tac), pos);
            } else if (p.curr_is_token(end_token)) {
                break;
            } else {
                next_tac = parse_tactic(p);
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

expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    p.next();
    parser::local_scope scope(p);
    p.clear_locals();
    expr tac  = parse_tactic(p);
    expr type = mk_tactic_unit();
    p.update_pos(tac, pos);
    expr r    = p.save_pos(mk_typed_expr(type, tac), pos);
    return p.save_pos(mk_by(r), pos);
}

expr parse_auto_quote_tactic_block(parser & p, unsigned, expr const *, pos_info const &) {
    expr r = parse_tactic(p);
    p.check_token_next(get_rbracket_tk(), "invalid auto-quote tactic block, ']' expected");
    return r;
}

void initialize_tactic_notation() {
    g_begin_end  = new name("begin_end");
    register_annotation(*g_begin_end);

    g_begin_end_element = new name("begin_end_element");
    register_annotation(*g_begin_end_element);
}

void finalize_tactic_notation() {
    delete g_begin_end;
    delete g_begin_end_element;
}
}
