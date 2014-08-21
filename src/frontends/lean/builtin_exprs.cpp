/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/annotation.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"

namespace lean {
namespace notation {
static name g_llevel_curly(".{"), g_rcurly("}"), g_in("in"), g_colon(":"), g_assign(":=");
static name g_comma(","), g_fact("[fact]"), g_inline("[inline]"), g_from("from"), g_using("using");
static name g_then("then"), g_have("have"), g_by("by"), g_qed("qed"), g_end("end");
static name g_take("take"), g_assume("assume"), g_show("show"), g_fun("fun");

static expr parse_Type(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.curr_is_token(g_llevel_curly)) {
        p.next();
        level l = p.parse_level();
        p.check_token_next(g_rcurly, "invalid Type expression, '}' expected");
        return p.save_pos(mk_sort(l), pos);
    } else {
        return p.save_pos(mk_sort(mk_level_placeholder()), pos);
    }
}

static expr parse_Type_prime(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_sort(mk_succ(mk_level_placeholder())), pos);
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

static expr mk_let(parser & p, name const & id, expr const & t, expr const & v, expr const & b, pos_info const & pos, binder_info const & bi) {
    expr l = p.save_pos(mk_let_annotation(p.save_pos(mk_lambda(id, t, b, bi), pos)), pos);
    return p.mk_app(l, v, pos);
}

static void parse_let_modifiers(parser & p, bool & is_fact, bool & is_opaque) {
    while (true) {
        if (p.curr_is_token(g_fact)) {
            is_fact = true;
            p.next();
        } else if (p.curr_is_token(g_inline)) {
            is_opaque = false;
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
        auto pos = p.pos();
        name id  = p.check_atomic_id_next("invalid let declaration, identifier expected");
        bool is_opaque = true;
        bool is_fact   = false;
        expr type, value;
        parse_let_modifiers(p, is_fact, is_opaque);
        if (p.curr_is_token(g_assign)) {
            p.next();
            if (is_opaque)
                type  = p.save_pos(mk_expr_placeholder(), pos);
            value = p.parse_expr();
        } else if (p.curr_is_token(g_colon)) {
            if (!is_opaque)
                throw parser_error("invalid let 'inline' declaration, explicit type must not be provided", p.pos());
            p.next();
            type = p.parse_expr();
            p.check_token_next(g_assign, "invalid declaration, ':=' expected");
            value = p.parse_expr();
        } else {
            parser::local_scope scope2(p);
            buffer<expr> ps;
            auto lenv = p.parse_binders(ps);
            if (p.curr_is_token(g_colon)) {
                if (!is_opaque)
                    throw parser_error("invalid let 'inline' declaration, explicit type must not be provided", p.pos());
                p.next();
                type  = p.parse_scoped_expr(ps, lenv);
            } else if (is_opaque) {
                type  = p.save_pos(mk_expr_placeholder(), pos);
            }
            p.check_token_next(g_assign, "invalid let declaration, ':=' expected");
            value = p.parse_scoped_expr(ps, lenv);
            if (is_opaque)
                type  = Pi(ps, type, p);
            value = Fun(ps, value, p);
        }
        if (is_opaque) {
            expr l = p.save_pos(mk_local(id, type), pos);
            p.add_local(l);
            expr body = abstract(parse_let_body(p, pos), l);
            return mk_let(p, id, type, value, body, pos, mk_contextual_info(is_fact));
        } else  {
            p.add_local_expr(id, value);
            return parse_let_body(p, pos);
        }
    }
}

static expr parse_let_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_let(p, pos);
}

static expr parse_placeholder(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_explicit_expr_placeholder(), pos);
}

static expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr t = p.parse_expr();
    return p.mk_by(t, pos);
}

static expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (!p.has_tactic_decls())
        throw parser_error("invalid 'begin-end' expression, tactic module has not been imported", pos);
    optional<expr> pre_tac = get_begin_end_pre_tactic(p.env());
    optional<expr> r;
    while (true) {
        bool use_exact = (p.curr_is_token(g_have) || p.curr_is_token(g_show) || p.curr_is_token(g_assume) ||
                          p.curr_is_token(g_take) || p.curr_is_token(g_fun));
        auto pos = p.pos();
        expr tac = p.parse_expr();
        if (use_exact)
            tac = p.mk_app(get_exact_tac_fn(), tac, pos);
        if (pre_tac)
            tac = p.mk_app({get_and_then_tac_fn(), *pre_tac, tac}, pos);
        tac = p.mk_app(get_determ_tac_fn(), tac, pos);
        r = r ? p.mk_app({get_and_then_tac_fn(), *r, tac}, pos) : tac;
        if (p.curr_is_token(g_end)) {
            auto pos = p.pos();
            p.next();
            return p.mk_by(*r, pos);
        } else if (p.curr_is_token(g_comma)) {
            p.next();
        } else {
            throw parser_error("invalid begin-end, ',' or 'end' expected", p.pos());
        }
    }
}

static expr parse_proof(parser & p, expr const & prop) {
    if (p.curr_is_token(g_from)) {
        // parse: 'from' expr
        p.next();
        return p.parse_expr();
    } else if (p.curr_is_token(g_by)) {
        // parse: 'by' tactic
        auto pos = p.pos();
        p.next();
        expr t = p.parse_expr();
        return p.mk_by(t, pos);
    } else if (p.curr_is_token(g_using)) {
        // parse: 'using' locals* ',' proof
        auto using_pos = p.pos();
        p.next();
        parser::local_scope scope(p);
        buffer<expr> locals;
        while (!p.curr_is_token(g_comma)) {
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
            pr = p.save_pos(pr(l), using_pos);
        }
        return pr;
    } else {
        throw parser_error("invalid expression, 'by', 'using' or 'from' expected", p.pos());
    }
}

static expr parse_have_core(parser & p, pos_info const & pos, optional<expr> const & prev_local) {
    auto id_pos       = p.pos();
    bool is_fact      = false;
    name id;
    expr prop;
    if (p.curr_is_token(g_fact)) {
        p.next();
        is_fact       = true;
        id            = p.mk_fresh_name();
        prop          = p.parse_expr();
    } else if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(g_fact)) {
            p.next();
            p.check_token_next(g_colon, "invalid 'have' declaration, ':' expected");
            is_fact   = true;
            prop      = p.parse_expr();
        } else if (p.curr_is_token(g_colon)) {
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
    p.check_token_next(g_comma, "invalid 'have' declaration, ',' expected");
    expr proof;
    if (prev_local) {
        parser::local_scope scope(p);
        p.add_local(*prev_local);
        auto proof_pos = p.pos();
        proof = parse_proof(p, prop);
        proof = p.save_pos(Fun(*prev_local, proof), proof_pos);
        proof = p.save_pos(proof(*prev_local), proof_pos);
    } else {
        proof = parse_proof(p, prop);
    }
    p.check_token_next(g_comma, "invalid 'have' declaration, ',' expected");
    parser::local_scope scope(p);
    binder_info bi = mk_contextual_info(is_fact);
    expr l = p.save_pos(mk_local(id, prop, bi), pos);
    p.add_local(l);
    expr body;
    if (p.curr_is_token(g_then)) {
        auto then_pos = p.pos();
        p.next();
        p.check_token_next(g_have, "invalid 'then have' declaration, 'have' expected");
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

static name H_show("H_show");
static expr parse_show(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr prop  = p.parse_expr();
    p.check_token_next(g_comma, "invalid 'show' declaration, ',' expected");
    expr proof = parse_proof(p, prop);
    return mk_let(p, H_show, prop, proof, Var(0), pos, mk_contextual_info(false));
}

static name g_exists_elim("exists_elim");
static expr parse_obtain(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (!p.env().find(g_exists_elim))
        throw parser_error("invalid use of 'obtain' expression, environment does not contain 'exists_elim' theorem", pos);
    // exists_elim {A : Type} {P : A → Prop} {B : Prop} (H1 : ∃ x : A, P x) (H2 : ∀ (a : A) (H : P a), B)
    buffer<expr> ps;
    auto b_pos = p.pos();
    environment env = p.parse_binders(ps);
    unsigned num_ps = ps.size();
    if (num_ps < 2)
        throw parser_error("invalid 'obtain' expression, at least 2 binders expected", b_pos);
    bool is_fact = false;
    if (p.curr_is_token(g_fact)) {
        p.next();
        is_fact = true;
    }
    if (!is_fact) {
        expr H = ps[num_ps-1];
        ps[num_ps-1] = update_local(H, mlocal_type(H), local_info(H).update_contextual(false));
    }
    p.check_token_next(g_comma, "invalid 'obtain' expression, ',' expected");
    p.check_token_next(g_from, "invalid 'obtain' expression, 'from' expected");
    expr H1 = p.parse_expr();
    p.check_token_next(g_comma, "invalid 'obtain' expression, ',' expected");
    expr b  = p.parse_scoped_expr(ps, env);
    expr H  = ps[num_ps-1];
    name H_name = local_pp_name(H);
    unsigned i = num_ps-1;
    while (i > 1) {
        --i;
        expr a      = ps[i];
        expr H_aux  = mk_local(p.mk_fresh_name(), H_name.append_after(i), mk_expr_placeholder(), mk_contextual_info(false));
        expr  H2    = Fun({a, H}, b);
        b = mk_constant(g_exists_elim)(H_aux, H2);
        H = H_aux;
    }
    expr a  = ps[0];
    expr H2 = Fun({a, H}, b);
    expr r  = mk_constant(g_exists_elim)(H1, H2);
    return p.rec_save_pos(r, pos);
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
    return p.save_pos(mk_explicit(e), pos);
}

static expr parse_including_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    buffer<expr> locals;
    while (!p.curr_is_token(g_comma)) {
        auto pos = p.pos();
        name id  = p.check_id_next("invalid 'including', identifier expected");
        if (auto it = p.get_local(id)) {
            locals.push_back(*it);
        } else {
            throw parser_error(sstream() << "invalid 'including', '" << id << "' is not a local declaraton", pos);
        }
    }
    p.next();
    parser::local_scope scope(p);
    buffer<expr> new_locals;
    for (auto old_l : locals) {
        binder_info bi = local_info(old_l);
        bi = bi.update_contextual(true);
        expr new_l     = p.save_pos(mk_local(local_pp_name(old_l), mk_as_is(mlocal_type(old_l)), bi), pos);
        p.add_local(new_l);
        new_locals.push_back(new_l);
    }
    expr r = Fun(new_locals, p.parse_expr(), p);
    r = p.rec_save_pos(mk_app(r, locals), pos);
    return r;
}

static expr parse_sorry(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.mk_sorry(pos);
}

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("_", mk_ext_action(parse_placeholder))}, x0);
    r = r.add({transition("by", mk_ext_action(parse_by))}, x0);
    r = r.add({transition("have", mk_ext_action(parse_have))}, x0);
    r = r.add({transition("show", mk_ext_action(parse_show))}, x0);
    r = r.add({transition("obtain", mk_ext_action(parse_obtain))}, x0);
    r = r.add({transition("(", Expr), transition(")", Skip)}, x0);
    r = r.add({transition("fun", Binders), transition(",", mk_scoped_expr_action(x0))}, x0);
    r = r.add({transition("Pi", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    r = r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    r = r.add({transition("Type'", mk_ext_action(parse_Type_prime))}, x0);
    r = r.add({transition("let", mk_ext_action(parse_let_expr))}, x0);
    r = r.add({transition("calc", mk_ext_action(parse_calc_expr))}, x0);
    r = r.add({transition("#", mk_ext_action(parse_overwrite_notation))}, x0);
    r = r.add({transition("@", mk_ext_action(parse_explicit_expr))}, x0);
    r = r.add({transition("begin", mk_ext_action(parse_begin_end))}, x0);
    r = r.add({transition("sorry", mk_ext_action(parse_sorry))}, x0);
    r = r.add({transition("including", mk_ext_action(parse_including_expr))}, x0);
    return r;
}

parse_table init_led_table() {
    parse_table r(false);
    r = r.add({transition("->", mk_expr_action(get_arrow_prec()-1))}, mk_arrow(Var(1), Var(1)));
    return r;
}
}
bool is_show_aux_name(name const & n) { return n == notation::H_show; }

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
