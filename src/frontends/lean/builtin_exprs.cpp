/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "library/annotation.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/aliases.h"
#include "library/scoped_ext.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/exact_tactic.h"
#include "library/tactic/util.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/let.h"
#include "library/definitional/equations.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/info_tactic.h"
#include "frontends/lean/info_annotation.h"

namespace lean {
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

static void parse_let_modifiers(parser & p, bool & is_visible) {
    while (true) {
        if (p.curr_is_token(get_visible_tk())) {
            is_visible = true;
            p.next();
        } else {
            break;
        }
    }
}

static expr parse_let(parser & p, pos_info const & pos) {
    parser::local_scope scope1(p);
    if (p.parse_local_notation_decl()) {
        return parse_let_body(p, pos);
    } else {
        auto id_pos     = p.pos();
        name id         = p.check_atomic_id_next("invalid let declaration, identifier expected");
        bool is_visible = false;
        optional<expr> type;
        expr value;
        parse_let_modifiers(p, is_visible);
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
            v = p.save_pos(mk_typed_expr(*type, value), p.pos_of(value));
        else
            v = value;
        v = p.save_pos(mk_let_value(v), id_pos);
        p.add_local_expr(id, v);
        expr b = parse_let_body(p, pos);
        return p.save_pos(mk_let(id, v, b), pos);
    }
}

static expr parse_let_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_let(p, pos);
}

static expr parse_placeholder(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_explicit_expr_placeholder(), pos);
}

static environment open_tactic_namespace(parser & p) {
    if (!is_tactic_namespace_open(p.env())) {
        environment env = using_namespace(p.env(), p.ios(), "tactic");
        env = add_aliases(env, name("tactic"), name());
        return env;
    } else {
        return p.env();
    }
}

static expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    environment env = open_tactic_namespace(p);
    parser::undef_id_to_local_scope scope(p);
    parser::local_scope scope2(p, env);
    parser::undef_id_to_local_scope scope1(p);
    p.next();
    expr t = p.parse_expr();
    return p.mk_by(t, pos);
}

static expr parse_begin_end_core(parser & p, pos_info const & pos) {
    if (!p.has_tactic_decls())
        throw parser_error("invalid 'begin-end' expression, tactic module has not been imported", pos);
    environment env = open_tactic_namespace(p);
    parser::local_scope scope2(p, env);
    parser::undef_id_to_local_scope scope1(p);
    p.next();
    optional<expr> pre_tac = get_begin_end_pre_tactic(env);
    buffer<expr> tacs;
    bool first = true;
    while (!p.curr_is_token(get_end_tk())) {
        if (first) {
            first = false;
        } else {
            auto pos = p.pos();
            p.check_token_next(get_comma_tk(), "invalid 'begin-end' expression, ',' expected");
            if (p.collecting_info()) {
                expr info_tac = p.save_pos(mk_info_tactic_expr(), pos);
                tacs.push_back(mk_begin_end_element_annotation(info_tac));
            }
        }
        if (p.curr_is_token(get_end_tk()))
            break;
        bool use_exact = (p.curr_is_token(get_have_tk()) || p.curr_is_token(get_show_tk()) ||
                          p.curr_is_token(get_assume_tk()) || p.curr_is_token(get_take_tk()) ||
                          p.curr_is_token(get_fun_tk()));
        auto pos = p.pos();
        expr tac = p.parse_expr();
        if (use_exact)
            tac = p.mk_app(get_exact_tac_fn(), tac, pos);
        if (pre_tac)
            tac = p.mk_app({get_and_then_tac_fn(), *pre_tac, tac}, pos);
        tac = mk_begin_end_element_annotation(tac);
        tacs.push_back(tac);
    }
    auto end_pos = p.pos();
    p.next();
    if (tacs.empty()) {
        expr tac = get_id_tac_fn();
        if (pre_tac)
            tac = p.mk_app({get_and_then_tac_fn(), *pre_tac, tac}, end_pos);
        tac = mk_begin_end_element_annotation(tac);
        tacs.push_back(tac);
    }
    expr r = tacs[0];
    if (tacs.size() == 1) {
        // Hack: for having a uniform squiggle placement for unsolved goals.
        // That is, the result is always of the form and_then(...).
        r = p.mk_app({get_and_then_tac_fn(), r, mk_begin_end_element_annotation(get_id_tac_fn())}, end_pos);
    }
    for (unsigned i = 1; i < tacs.size(); i++) {
        r = p.mk_app({get_and_then_tac_fn(), r, tacs[i]}, end_pos);
    }
    return p.mk_by(mk_begin_end_annotation(r), end_pos);
}

static expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_begin_end_core(p, pos);
}

static expr parse_proof_qed_core(parser & p, pos_info const & pos) {
    expr r = p.save_pos(mk_proof_qed_annotation(p.parse_expr()), pos);
    p.check_token_next(get_qed_tk(), "invalid proof-qed, 'qed' expected");
    return r;
}

static expr parse_proof(parser & p, expr const & prop) {
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
        return parse_begin_end_core(p, pos);
    } else if (p.curr_is_token(get_by_tk())) {
        // parse: 'by' tactic
        auto pos = p.pos();
        p.next();
        expr t = p.parse_expr();
        return p.mk_by(t, pos);
    } else if (p.curr_is_token(get_using_tk())) {
        // parse: 'using' locals* ',' proof
        auto using_pos = p.pos();
        p.next();
        parser::local_scope scope(p);
        buffer<expr> locals;
        while (!p.curr_is_token(get_comma_tk())) {
            auto id_pos = p.pos();
            expr l      = p.parse_expr();
            if (!is_local(l))
                throw parser_error("invalid 'using' declaration for 'have', local expected", id_pos);
            p.add_local(l);
            locals.push_back(l);
        }
        p.next(); // consume ','
        expr pr = parse_proof(p, prop);
        unsigned i = locals.size();
        while (i > 0) {
            --i;
            expr l = locals[i];
            pr = p.save_pos(Fun(l, pr), using_pos);
            pr = p.save_pos(mk_app(pr, l), using_pos);
        }
        return pr;
    } else {
        throw parser_error("invalid expression, 'by', 'using' or 'from' expected", p.pos());
    }
}

static expr parse_have_core(parser & p, pos_info const & pos, optional<expr> const & prev_local) {
    auto id_pos       = p.pos();
    bool is_visible   = false;
    name id;
    expr prop;
    if (p.curr_is_token(get_visible_tk())) {
        p.next();
        is_visible    = true;
        id            = p.mk_fresh_name();
        prop          = p.parse_expr();
    } else if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_visible_tk())) {
            p.next();
            p.check_token_next(get_colon_tk(), "invalid 'have' declaration, ':' expected");
            is_visible = true;
            prop       = p.parse_expr();
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            prop      = p.parse_expr();
        } else {
            expr left = p.id_to_expr(id, id_pos);
            id        = p.mk_fresh_name();
            prop      = p.parse_led(left);
        }
    } else {
        id            = p.mk_fresh_name();
        prop          = p.parse_expr();
    }
    p.check_token_next(get_comma_tk(), "invalid 'have' declaration, ',' expected");
    expr proof;
    if (prev_local) {
        parser::local_scope scope(p);
        p.add_local(*prev_local);
        auto proof_pos = p.pos();
        proof = parse_proof(p, prop);
        proof = p.save_pos(Fun(*prev_local, proof), proof_pos);
        proof = p.save_pos(mk_app(proof, *prev_local), proof_pos);
    } else {
        proof = parse_proof(p, prop);
    }
    p.check_token_next(get_comma_tk(), "invalid 'have' declaration, ',' expected");
    parser::local_scope scope(p);
    binder_info bi = mk_contextual_info(is_visible);
    expr l = p.save_pos(mk_local(id, prop, bi), pos);
    p.add_local(l);
    expr body;
    if (p.curr_is_token(get_then_tk())) {
        auto then_pos = p.pos();
        p.next();
        p.check_token_next(get_have_tk(), "invalid 'then have' declaration, 'have' expected");
        body  = parse_have_core(p, then_pos, some_expr(l));
    } else {
        body  = p.parse_expr();
    }
    // remark: mk_contextual_info(false) informs the elaborator that prop should not occur inside metavariables.
    body = abstract(body, l);
    expr r = p.save_pos(mk_have_annotation(p.save_pos(mk_lambda(id, prop, body, bi), pos)), pos);
    return p.mk_app(r, proof, pos);
}

static expr parse_have(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_have_core(p, pos, none_expr());
}

static name * H_show = nullptr;
static expr parse_show(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr prop  = p.parse_expr();
    p.check_token_next(get_comma_tk(), "invalid 'show' declaration, ',' expected");
    expr proof = parse_proof(p, prop);
    expr b = p.save_pos(mk_lambda(*H_show, prop, Var(0)), pos);
    expr r = p.mk_app(b, proof, pos);
    return p.save_pos(mk_show_annotation(r), pos);
}

static name * g_exists_elim = nullptr;
static expr parse_obtain(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (!p.env().find(*g_exists_elim))
        throw parser_error("invalid use of 'obtain' expression, environment does not contain 'exists.elim' theorem", pos);
    // exists_elim {A : Type} {P : A → Prop} {B : Prop} (H1 : ∃ x : A, P x) (H2 : ∀ (a : A) (H : P a), B)
    buffer<expr> ps;
    auto b_pos = p.pos();
    unsigned rbp = 0;
    environment env = p.parse_binders(ps, rbp);
    unsigned num_ps = ps.size();
    if (num_ps < 2)
        throw parser_error("invalid 'obtain' expression, at least 2 binders expected", b_pos);
    bool is_visible = false;
    if (p.curr_is_token(get_visible_tk())) {
        p.next();
        is_visible = true;
    }
    if (!is_visible) {
        expr H = ps[num_ps-1];
        ps[num_ps-1] = update_local(H, mlocal_type(H), local_info(H).update_contextual(false));
    }
    p.check_token_next(get_comma_tk(), "invalid 'obtain' expression, ',' expected");
    p.check_token_next(get_from_tk(), "invalid 'obtain' expression, 'from' expected");
    expr H1 = p.parse_expr();
    p.check_token_next(get_comma_tk(), "invalid 'obtain' expression, ',' expected");
    expr b  = p.parse_scoped_expr(ps, env);
    expr H  = ps[num_ps-1];
    name H_name = local_pp_name(H);
    unsigned i = num_ps-1;
    while (i > 1) {
        --i;
        expr a      = ps[i];
        expr H_aux  = mk_local(p.mk_fresh_name(), H_name.append_after(i), mk_expr_placeholder(), mk_contextual_info(false));
        expr  H2    = Fun({a, H}, b);
        b = mk_app(mk_constant(*g_exists_elim), H_aux, H2);
        H = H_aux;
    }
    expr a  = ps[0];
    expr H2 = Fun({a, H}, b);
    expr r  = mk_app(mk_constant(*g_exists_elim), H1, H2);
    return p.rec_save_pos(r, pos);
}

static name * g_ite  = nullptr;
static name * g_dite = nullptr;
static expr * g_not  = nullptr;
static unsigned g_then_else_prec = 45;

static expr parse_ite(parser & p, expr const & c, pos_info const & pos) {
    if (!p.env().find(*g_ite))
        throw parser_error("invalid use of 'if-then-else' expression, environment does not contain 'ite' definition", pos);
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t = p.parse_expr(g_then_else_prec);
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    expr e = p.parse_expr(g_then_else_prec);
    return mk_app(mk_constant(*g_ite), c, t, e);
}

static expr parse_dite(parser & p, name const & H_name, pos_info const & pos) {
    if (!p.env().find(*g_dite))
        throw parser_error("invalid use of (dependent) 'if-then-else' expression, environment does "
                           "not contain 'dite' definition", pos);
    expr c = p.parse_expr();
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t, e;
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, c);
        p.add_local(H);
        t = Fun(H, p.parse_expr(g_then_else_prec));
    }
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, mk_app(*g_not, c));
        p.add_local(H);
        e = Fun(H, p.parse_expr(g_then_else_prec));
    }
    return mk_app(mk_constant(*g_dite), c, t, e);
}

static expr parse_if_then_else(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.curr_is_identifier()) {
        auto id_pos = p.pos();
        name id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            return parse_dite(p, id, pos);
        } else {
            expr e = p.id_to_expr(id, id_pos);
            while (!p.curr_is_token(get_then_tk())) {
                e = p.parse_led(e);
            }
            return parse_ite(p, e, pos);
        }
    } else {
        expr c = p.parse_expr();
        return parse_ite(p, c, pos);
    }
}

static expr parse_calc_expr(parser & p, unsigned, expr const *, pos_info const &) {
    return parse_calc(p);
}

static expr parse_overwrite_notation(parser & p, unsigned, expr const *, pos_info const &) {
    name n = p.check_id_next("invalid '#' local notation, identifier expected");
    environment env = overwrite_notation(p.env(), n);
    return p.parse_scoped_expr(0, nullptr, env);
}

static expr parse_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr(get_max_prec());
    if (is_choice(e)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(e); i++)
            new_choices.push_back(p.save_pos(mk_explicit(get_choice(e, i)), pos));
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_explicit(e), pos);
    }
}

static expr parse_consume_args_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr(get_max_prec());
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

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("_", mk_ext_action(parse_placeholder))}, x0);
    r = r.add({transition("by", mk_ext_action_core(parse_by))}, x0);
    r = r.add({transition("have", mk_ext_action(parse_have))}, x0);
    r = r.add({transition("show", mk_ext_action(parse_show))}, x0);
    r = r.add({transition("obtain", mk_ext_action(parse_obtain))}, x0);
    r = r.add({transition("if", mk_ext_action(parse_if_then_else))}, x0);
    r = r.add({transition("(", Expr), transition(")", mk_ext_action(parse_rparen))}, x0);
    r = r.add({transition("?(", Expr), transition(")", mk_ext_action(parse_inaccessible))}, x0);
    r = r.add({transition("⌞", Expr), transition("⌟", mk_ext_action(parse_inaccessible))}, x0);
    r = r.add({transition("fun", Binders), transition(",", mk_scoped_expr_action(x0))}, x0);
    r = r.add({transition("Pi", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    r = r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    r = r.add({transition("let", mk_ext_action(parse_let_expr))}, x0);
    r = r.add({transition("calc", mk_ext_action(parse_calc_expr))}, x0);
    r = r.add({transition("#", mk_ext_action(parse_overwrite_notation))}, x0);
    r = r.add({transition("@", mk_ext_action(parse_explicit_expr))}, x0);
    r = r.add({transition("!", mk_ext_action(parse_consume_args_expr))}, x0);
    r = r.add({transition("begin", mk_ext_action_core(parse_begin_end))}, x0);
    r = r.add({transition("proof", mk_ext_action(parse_proof_qed))}, x0);
    r = r.add({transition("sorry", mk_ext_action(parse_sorry))}, x0);
    r = r.add({transition("match", mk_ext_action(parse_match))}, x0);
    return r;
}

parse_table init_led_table() {
    parse_table r(false);
    r = r.add({transition("->", mk_expr_action(get_arrow_prec()-1))},    mk_arrow(Var(1), Var(1)));
    r = r.add({transition("<d", mk_expr_action(get_decreasing_prec()))}, mk_decreasing(Var(1), Var(0)));
    return r;
}
}
bool is_show_aux_name(name const & n) { return n == *notation::H_show; }

static parse_table * g_nud_table = nullptr;
static parse_table * g_led_table = nullptr;

parse_table get_builtin_nud_table() {
    return *g_nud_table;
}

parse_table get_builtin_led_table() {
    return *g_led_table;
}

void initialize_builtin_exprs() {
    notation::H_show        = new name("H_show");
    notation::g_exists_elim = new name{"exists", "elim"};
    notation::g_ite         = new name("ite");
    notation::g_dite        = new name("dite");
    notation::g_not         = new expr(mk_constant("not"));
    g_nud_table             = new parse_table();
    *g_nud_table            = notation::init_nud_table();
    g_led_table             = new parse_table();
    *g_led_table            = notation::init_led_table();
}

void finalize_builtin_exprs() {
    delete g_led_table;
    delete g_nud_table;
    delete notation::H_show;
    delete notation::g_exists_elim;
    delete notation::g_ite;
    delete notation::g_dite;
    delete notation::g_not;
}
}
