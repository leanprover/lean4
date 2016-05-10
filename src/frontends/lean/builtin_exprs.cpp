/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "library/annotation.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/aliases.h"
#include "library/scoped_ext.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/let.h"
#include "library/constants.h"
#include "library/definitional/equations.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/info_annotation.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/obtain_expr.h"
#include "frontends/lean/nested_declaration.h"

#ifndef LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE
#define LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE true
#endif

namespace lean {
static name * g_parser_checkpoint_have = nullptr;

bool get_parser_checkpoint_have(options const & opts) {
    return opts.get_bool(*g_parser_checkpoint_have, LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE);
}

namespace notation {
static expr parse_Type(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        level l = p.parse_level();
        p.check_token_next(get_rcurly_tk(), "invalid Type expression, '}' expected");
        return p.save_pos(mk_sort(l), pos);
    } else {
        return p.save_pos(mk_sort(mk_level_placeholder()), pos);
    }
}

static expr parse_let(parser & p, pos_info const & pos);
static expr parse_let_body(parser & p, pos_info const & pos) {
    if (p.curr_is_token(get_comma_tk())) {
        p.next();
        return parse_let(p, pos);
    } else if (p.curr_is_token(get_in_tk())) {
        p.next();
        return p.parse_expr();
    } else {
        throw parser_error("invalid let declaration, 'in' or ',' expected", p.pos());
    }
}

// Distribute mk_typed_expr over choice expression.
// see issue #768
static expr mk_typed_expr_distrib_choice(parser & p, expr const & type, expr const & value, pos_info const & pos) {
    if (is_choice(value)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(value); i++) {
            new_choices.push_back(mk_typed_expr_distrib_choice(p, type, get_choice(value, i), pos));
        }
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_typed_expr(type, value), pos);
    }
}

static expr parse_let(parser & p, pos_info const & pos) {
    parser::local_scope scope1(p);
    if (p.parse_local_notation_decl()) {
        return parse_let_body(p, pos);
    } else {
        auto id_pos     = p.pos();
        name id         = p.check_atomic_id_next("invalid let declaration, atomic identifier expected");
        optional<expr> type;
        expr value;
        if (p.curr_is_token(get_assign_tk())) {
            p.next();
            value = p.parse_expr();
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            type = p.parse_expr();
            p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
            value = p.parse_expr();
        } else {
            parser::local_scope scope2(p);
            buffer<expr> ps;
            unsigned rbp = 0;
            auto lenv = p.parse_binders(ps, rbp);
            if (p.curr_is_token(get_colon_tk())) {
                p.next();
                type  = p.parse_scoped_expr(ps, lenv);
                type  = Pi(ps, *type, p);
            }
            p.check_token_next(get_assign_tk(), "invalid let declaration, ':=' expected");
            value = p.parse_scoped_expr(ps, lenv);
            value = Fun(ps, value, p);
        }
        expr v;
        if (type)
            v = mk_typed_expr_distrib_choice(p, *type, value, p.pos_of(value));
        else
            v = value;
        v = p.save_pos(mk_let_value(v), id_pos);
        p.add_local_expr(id, v);
        expr b = parse_let_body(p, pos);
        // TODO(Leo): use let-expression after we reimplement elaborator
        return p.save_pos(mk_let_macro(id, v, b), pos);
    }
}

static expr parse_let_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_let(p, pos);
}

static expr parse_placeholder(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_explicit_expr_placeholder(), pos);
}

static expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    throw parser_error("by-exprs have been disabled", pos);
}

static expr parse_begin_end_core(parser & p, pos_info const & start_pos,
                                 name const & end_token, bool nested = false) {
    throw parser_error("begin-end-exprs have been disabled", start_pos);
}

static expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_begin_end_core(p, pos, get_end_tk());
}

static expr parse_tactic_expr(parser & p, unsigned, expr const *, pos_info const &) {
    return p.parse_tactic();
}

static expr parse_proof_qed_core(parser & p, pos_info const & pos) {
    throw parser_error("proof-qed-exprs have been disabled", pos);
}

static expr parse_proof(parser & p);

static expr parse_using_expr(parser & p, pos_info const & using_pos) {
    parser::local_scope scope(p);
    buffer<expr> locals;
    buffer<expr> new_locals;
    while (!p.curr_is_token(get_comma_tk())) {
        auto id_pos = p.pos();
        expr l      = p.parse_id();
        if (!is_local(l))
            throw parser_error("invalid 'using' declaration, local expected", id_pos);
        expr new_l;
        binder_info bi = local_info(l);
        if (p.is_local_variable_parameter(local_pp_name(l))) {
            expr new_type = p.save_pos(mk_as_is(mlocal_type(l)), id_pos);
            new_l = p.save_pos(mk_local(mlocal_name(l), local_pp_name(l), new_type, bi), id_pos);
        } else {
            new_l = p.save_pos(update_local(l, bi), id_pos);
        }
        p.add_local(new_l);
        locals.push_back(l);
        new_locals.push_back(new_l);
    }
    p.next(); // consume ','
    expr pr = p.parse_expr();
    unsigned i = locals.size();
    while (i > 0) {
        --i;
        expr l     = locals[i];
        expr new_l = new_locals[i];
        pr = p.save_pos(Fun(new_l, pr), using_pos);
        pr = p.save_pos(mk_app(pr, l), using_pos);
    }
    return pr;
}

static expr parse_using(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_using_expr(p, pos);
}

static expr parse_proof(parser & p) {
    if (p.curr_is_token(get_from_tk())) {
        // parse: 'from' expr
        p.next();
        return p.parse_expr();
    } else if (p.curr_is_token(get_proof_tk())) {
        auto pos = p.pos();
        p.next();
        return parse_proof_qed_core(p, pos);
    } else if (p.curr_is_token(get_begin_tk())) {
        auto pos = p.pos();
        return parse_begin_end_core(p, pos, get_end_tk());
    } else if (p.curr_is_token(get_by_tk())) {
        auto pos = p.pos();
        return parse_by(p, 0, nullptr, pos);
    } else {
        throw parser_error("invalid expression, 'by', 'begin', 'proof', 'using' or 'from' expected", p.pos());
    }
}

static expr parse_have_core(parser & p, pos_info const & pos, optional<expr> const & prev_local) {
    auto id_pos       = p.pos();
    name id;
    expr prop;
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            prop      = p.parse_expr();
        } else {
            expr left = p.id_to_expr(id, id_pos);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_expr_lbp()) {
                left = p.parse_led(left);
            }
            prop      = left;
        }
    } else {
        id            = get_this_tk();
        prop          = p.parse_expr();
    }
    expr proof;
    if (p.curr_is_token(get_bar_tk()) && !prev_local) {
        expr fn = p.save_pos(mk_local(id, prop, mk_rec_info(true)), id_pos);
        proof = parse_local_equations(p, fn);
    } else {
        p.check_token_next(get_comma_tk(), "invalid 'have/assert' declaration, ',' expected");
        if (prev_local) {
            parser::local_scope scope(p);
            p.add_local(*prev_local);
            auto proof_pos = p.pos();
            proof = parse_proof(p);
            proof = p.save_pos(Fun(*prev_local, proof), proof_pos);
            proof = p.save_pos(mk_app(proof, *prev_local), proof_pos);
        } else {
            proof = parse_proof(p);
        }
    }
    p.check_token_next(get_comma_tk(), "invalid 'have/assert' declaration, ',' expected");
    parser::local_scope scope(p);
    expr l = p.save_pos(mk_local(id, prop), pos);
    p.add_local(l);
    expr body;
    if (p.curr_is_token(get_then_tk())) {
        auto then_pos = p.pos();
        p.next();
        if (p.curr_is_token(get_assert_tk())) {
            p.next();
        } else {
            p.check_token_next(get_have_tk(), "invalid 'then' declaration, 'have' or 'assert' expected");
        }
        body  = parse_have_core(p, then_pos, some_expr(l));
    } else {
        body  = p.parse_expr();
    }
    body = abstract(body, l);
    if (get_parser_checkpoint_have(p.get_options()))
        body = mk_checkpoint_annotation(body);
    expr r = p.save_pos(mk_have_annotation(p.save_pos(mk_lambda(id, prop, body), pos)), pos);
    return p.mk_app(r, proof, pos);
}

static expr parse_have(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_have_core(p, pos, none_expr());
}

static expr parse_suppose(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto id_pos = p.pos();
    name id;
    expr prop;
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            prop      = p.parse_expr();
        } else {
            expr left = p.id_to_expr(id, id_pos);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_expr_lbp()) {
                left = p.parse_led(left);
            }
            prop      = left;
        }
    } else {
        id    = get_this_tk();
        prop  = p.parse_expr();
    }
    p.check_token_next(get_comma_tk(), "invalid 'suppose', ',' expected");
    parser::local_scope scope(p);
    expr l = p.save_pos(mk_local(id, prop), id_pos);
    p.add_local(l);
    expr body = p.parse_expr();
    return p.save_pos(Fun(l, body), pos);
}

static expr parse_show(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr prop  = p.parse_expr();
    if (p.curr_is_token(get_bar_tk())) {
        expr fn = p.save_pos(mk_local(get_this_tk(), prop, mk_rec_info(true)), pos);
        return parse_local_equations(p, fn);
    } else {
        p.check_token_next(get_comma_tk(), "invalid 'show' declaration, ',' expected");
        expr proof = parse_proof(p);
        expr b = p.save_pos(mk_lambda(get_this_tk(), prop, Var(0)), pos);
        expr r = p.mk_app(b, proof, pos);
        return p.save_pos(mk_show_annotation(r), pos);
    }
}

static expr parse_suffices_to_show(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto prop_pos = p.pos();
    name id;
    expr from;
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            from = p.parse_expr();
        } else {
            expr left = p.id_to_expr(id, prop_pos);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_expr_lbp()) {
                left = p.parse_led(left);
            }
            from = left;
        }
    } else {
        id    = get_this_tk();
        from  = p.parse_expr();
    }
    expr to    = p.save_pos(mk_expr_placeholder(), prop_pos);
    expr prop  = p.save_pos(mk_arrow(from, to), prop_pos);
    expr local = p.save_pos(mk_local(id, from), prop_pos);
    p.check_token_next(get_comma_tk(), "invalid 'suffices' declaration, ',' expected");
    expr body;
    {
        parser::local_scope scope(p);
        p.add_local(local);
        body = parse_proof(p);
    }
    expr proof = p.save_pos(Fun(local, body), pos);
    p.check_token_next(get_comma_tk(), "invalid 'suffices' declaration, ',' expected");
    expr rest  = p.parse_expr();
    expr r = p.mk_app(proof, rest, pos);
    return r;
}

static obtain_struct parse_obtain_decls (parser & p, buffer<expr> & ps) {
    buffer<obtain_struct> children;
    parser::local_scope scope(p);
    while (!p.curr_is_token(get_comma_tk()) && !p.curr_is_token(get_rbracket_tk())) {
        if (p.curr_is_token(get_lbracket_tk())) {
            p.next();
            auto s = parse_obtain_decls(p, ps);
            children.push_back(s);
            p.check_token_next(get_rbracket_tk(), "invalid 'obtain' expression, ']' expected");
        } else {
            unsigned rbp = 0;
            buffer<expr> new_ps;
            p.parse_simple_binders(new_ps, rbp);
            for (expr const & l : new_ps) {
                ps.push_back(l);
                p.add_local(l);
                children.push_back(obtain_struct());
            }
        }
    }
    if (children.empty())
        throw parser_error("invalid 'obtain' expression, empty declaration block", p.pos());
    return obtain_struct(to_list(children));
}

static name * H_obtain_from = nullptr;

static expr parse_obtain(parser & p, unsigned, expr const *, pos_info const & pos) {
    throw parser_error("obtain-exprs have been disabled", pos);
}

static expr * g_not  = nullptr;
static unsigned g_then_else_prec = 45;

static expr parse_ite(parser & p, expr const & c, pos_info const & pos) {
    if (!p.env().find(get_ite_name()))
        throw parser_error("invalid use of 'if-then-else' expression, environment does not contain 'ite' definition", pos);
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t = p.parse_expr(g_then_else_prec);
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    expr e = p.parse_expr(g_then_else_prec);
    return p.save_pos(mk_app(mk_constant(get_ite_name()), c, t, e), pos);
}

static expr parse_dite(parser & p, name const & H_name, expr const & c, pos_info const & pos) {
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t, e;
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, c);
        p.add_local(H);
        auto pos = p.pos();
        t = p.save_pos(Fun(H, p.parse_expr(g_then_else_prec)), pos);
    }
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, mk_app(*g_not, c));
        p.add_local(H);
        auto pos = p.pos();
        e = p.save_pos(Fun(H, p.parse_expr(g_then_else_prec)), pos);
    }
    return p.save_pos(mk_app(p.save_pos(mk_constant(get_dite_name()), pos), c, t, e), pos);
}

static expr parse_if_then_else(parser & p, unsigned, expr const *, pos_info const & pos) {
    pair<optional<name>, expr> ie = p.parse_qualified_expr();
    if (ie.first)
        return parse_dite(p, *ie.first, ie.second, pos);
    else
        return parse_ite(p, ie.second, pos);
}

static expr parse_calc_expr(parser & p, unsigned, expr const *, pos_info const &) {
    return parse_calc(p);
}

static expr parse_override_notation(parser & p, unsigned, expr const *, pos_info const &) {
    name n = p.check_id_next("invalid '#' local notation, identifier expected");
    bool persistent = false;
    environment env = override_notation(p.env(), n, persistent);
    env = overwrite_aliases(env, n, name());
    return p.parse_expr_with_env(env);
}

static expr parse_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr(get_Max_prec());
    if (is_choice(e)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(e); i++)
            new_choices.push_back(p.save_pos(mk_explicit(get_choice(e, i)), pos));
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_explicit(e), pos);
    }
}

static expr parse_partial_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr(get_Max_prec());
    if (is_choice(e)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(e); i++)
            new_choices.push_back(p.save_pos(mk_partial_explicit(get_choice(e, i)), pos));
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_partial_explicit(e), pos);
    }
}

static expr parse_consume_args_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr(get_Max_prec());
    if (is_choice(e)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(e); i++)
            new_choices.push_back(p.save_pos(mk_consume_args(get_choice(e, i)), pos));
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_consume_args(e), pos);
    }
}

static expr parse_sorry(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.mk_sorry(pos);
}

static expr parse_rparen(parser & p, unsigned, expr const * args, pos_info const & pos) {
    if (p.collecting_info())
        return p.save_pos(mk_extra_info(args[0], nulltag), pos);
    else
        return args[0];
}

static expr parse_proof_qed(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_proof_qed_core(p, pos);
}

static expr parse_inaccessible(parser & p, unsigned, expr const * args, pos_info const & pos) {
    return p.save_pos(mk_inaccessible(args[0]), pos);
}

static expr parse_typed_expr(parser & p, unsigned, expr const * args, pos_info const & pos) {
    return mk_typed_expr_distrib_choice(p, args[1], args[0], pos);
}

static expr parse_pattern(parser & p, unsigned, expr const * args, pos_info const & pos) {
    // return p.save_pos(mk_pattern_hint(args[0]), pos);
    throw parser_error("pattern_hints have been disabled", pos);
}

static expr parse_do(parser & p, unsigned, expr const *, pos_info const & pos) {
    parser::local_scope scope(p);
    buffer<expr> es;
    buffer<expr> locals;
    bool has_braces = false;
    if (p.curr_is_token(get_lcurly_tk())) {
        has_braces = true;
        p.next();
    }
    while (true) {
        expr curr;
        optional<name> id;
        auto id_pos = p.pos();
        if (p.curr_is_identifier()) {
            id = p.get_name_val();
            p.next();
            if (p.curr_is_token(get_larrow_tk())) {
                p.next();
                curr = p.parse_expr();
            } else {
                expr left = p.id_to_expr(*id, id_pos);
                id        = optional<name>();
                unsigned rbp = 0;
                while (rbp < p.curr_expr_lbp()) {
                    left = p.parse_led(left);
                }
                curr = left;
            }
        } else {
            id   = optional<name>();
            curr = p.parse_expr();
        }
        es.push_back(curr);
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
            name n = id ? *id : mk_fresh_name();
            expr l = p.save_pos(mk_local(n, mk_expr_placeholder()), id_pos);
            p.add_local(l);
            locals.push_back(l);
        } else {
            if (id) {
                throw parser_error("invalid 'do' expression, unnecessary binder", id_pos);
            }
            break;
        }
    }
    if (has_braces) {
        p.check_token_next(get_rcurly_tk(), "invalid 'do' expression, '}' expected");
    }
    lean_assert(!es.empty());
    lean_assert(es.size() == locals.size() + 1);
    if (es.size() == 1)
        return es[0];
    unsigned i = es.size();
    --i;
    expr r = es[i];
    while (i > 0) {
        --i;
        r = mk_app(mk_constant(get_monad_bind_name()), es[i], Fun(locals[i], r));
    }
    return r;
}

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("_", mk_ext_action(parse_placeholder))}, x0);
    r = r.add({transition("by", mk_ext_action_core(parse_by))}, x0);
    r = r.add({transition("have", mk_ext_action(parse_have))}, x0);
    r = r.add({transition("assert", mk_ext_action(parse_have))}, x0);
    r = r.add({transition("suppose", mk_ext_action(parse_suppose))}, x0);
    r = r.add({transition("show", mk_ext_action(parse_show))}, x0);
    r = r.add({transition("suffices", mk_ext_action(parse_suffices_to_show))}, x0);
    r = r.add({transition("obtain", mk_ext_action(parse_obtain))}, x0);
    r = r.add({transition("abstract", mk_ext_action(parse_nested_declaration))}, x0);
    r = r.add({transition("if", mk_ext_action(parse_if_then_else))}, x0);
    r = r.add({transition("(", Expr), transition(")", mk_ext_action(parse_rparen))}, x0);
    r = r.add({transition("(", Expr), transition(":", Expr), transition(")", mk_ext_action(parse_typed_expr))}, x0);
    r = r.add({transition("?(", Expr), transition(")", mk_ext_action(parse_inaccessible))}, x0);
    r = r.add({transition("⌞", Expr), transition("⌟", mk_ext_action(parse_inaccessible))}, x0);
    r = r.add({transition("(:", Expr), transition(":)", mk_ext_action(parse_pattern))}, x0);
    r = r.add({transition("fun", Binders), transition(",", mk_scoped_expr_action(x0))}, x0);
    r = r.add({transition("Pi", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    r = r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    r = r.add({transition("let", mk_ext_action(parse_let_expr))}, x0);
    r = r.add({transition("calc", mk_ext_action(parse_calc_expr))}, x0);
    r = r.add({transition("#", mk_ext_action(parse_override_notation))}, x0);
    r = r.add({transition("#tactic", mk_ext_action(parse_tactic_expr))}, x0);
    r = r.add({transition("@", mk_ext_action(parse_explicit_expr))}, x0);
    r = r.add({transition("@@", mk_ext_action(parse_partial_explicit_expr))}, x0);
    r = r.add({transition("!", mk_ext_action(parse_consume_args_expr))}, x0);
    r = r.add({transition("begin", mk_ext_action_core(parse_begin_end))}, x0);
    r = r.add({transition("proof", mk_ext_action(parse_proof_qed))}, x0);
    r = r.add({transition("using", mk_ext_action(parse_using))}, x0);
    r = r.add({transition("sorry", mk_ext_action(parse_sorry))}, x0);
    r = r.add({transition("match", mk_ext_action(parse_match))}, x0);
    r = r.add({transition("do", mk_ext_action(parse_do))}, x0);
    init_structure_instance_parsing_rules(r);
    return r;
}

parse_table init_led_table() {
    parse_table r(false);
    r = r.add({transition("->", mk_expr_action(get_arrow_prec()-1))},    mk_arrow(Var(1), Var(1)));
    r = r.add({transition("<d", mk_expr_action(get_decreasing_prec()))}, mk_decreasing(Var(1), Var(0)));
    return r;
}
}

static parse_table * g_nud_table = nullptr;
static parse_table * g_led_table = nullptr;

parse_table get_builtin_nud_table() {
    return *g_nud_table;
}

parse_table get_builtin_led_table() {
    return *g_led_table;
}

void initialize_builtin_exprs() {
    notation::H_obtain_from = new name("H_obtain_from");
    notation::g_not         = new expr(mk_constant(get_not_name()));
    g_nud_table             = new parse_table();
    *g_nud_table            = notation::init_nud_table();
    g_led_table             = new parse_table();
    *g_led_table            = notation::init_led_table();

    g_parser_checkpoint_have = new name{"parser", "checkpoint_have"};
    register_bool_option(*g_parser_checkpoint_have, LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE,
                         "(parser) introduces a checkpoint on have-expressions, checkpoints are like Prolog-cuts");
}

void finalize_builtin_exprs() {
    delete g_led_table;
    delete g_nud_table;
    delete notation::H_obtain_from;
    delete notation::g_not;
    delete g_parser_checkpoint_have;
}
}
