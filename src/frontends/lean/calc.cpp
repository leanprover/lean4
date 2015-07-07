/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include <algorithm>
#include <vector>
#include "util/optional.h"
#include "util/name.h"
#include "util/rb_map.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "kernel/environment.h"
#include "library/relation_manager.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/choice.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/scoped_ext.h"
#include "library/annotation.h"
#include "library/typed_expr.h"
#include "library/sorry.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/begin_end_ext.h"

namespace lean {
static name * g_calc_name  = nullptr;

static expr mk_calc_annotation_core(expr const & e) { return mk_annotation(*g_calc_name, e); }
static expr mk_calc_annotation(expr const & pr) {
    if (is_by(pr) || is_begin_end_annotation(pr) || is_sorry(pr)) {
        return pr;
    } else {
        return mk_calc_annotation_core(pr);
    }
}
bool is_calc_annotation(expr const & e) { return is_annotation(e, *g_calc_name); }

typedef std::tuple<name, expr, expr>  calc_pred;
typedef pair<calc_pred, expr>         calc_step;
inline name const & pred_op(calc_pred const & p) { return std::get<0>(p); }
inline expr const & pred_lhs(calc_pred const & p) { return std::get<1>(p); }
inline expr const & pred_rhs(calc_pred const & p) { return std::get<2>(p); }
inline calc_pred const & step_pred(calc_step const & s) { return s.first; }
inline expr const & step_proof(calc_step const & s) { return s.second; }

static void decode_expr_core(expr const & e, buffer<calc_pred> & preds) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (!is_constant(fn))
        return;
    unsigned nargs = args.size();
    if (nargs < 2)
        return;
    preds.emplace_back(const_name(fn), args[nargs-2], args[nargs-1]);
}

// Check whether e is of the form (f ...) where f is a constant. If it is return f.
static void decode_expr(expr const & e, buffer<calc_pred> & preds, pos_info const & pos) {
    preds.clear();
    if (is_choice(e)) {
        for (unsigned i = 0; i < get_num_choices(e); i++)
            decode_expr_core(get_choice(e, i), preds);
    } else {
        decode_expr_core(e, preds);
    }
    if (preds.empty())
        throw parser_error("invalid 'calc' expression, expression must be a function application 'f a_1 ... a_k' "
                           "where f is a constant, and k >= 2", pos);
}

// Create (op _ _ ... _)
static expr mk_op_fn(parser & p, name const & op, unsigned num_placeholders, pos_info const & pos) {
    expr r = p.save_pos(mk_explicit(mk_constant(op)), pos);
    while (num_placeholders > 0) {
        num_placeholders--;
        r = p.mk_app(r, p.save_pos(mk_expr_placeholder(), pos), pos);
    }
    return r;
}

static void parse_calc_proof(parser & p, buffer<calc_pred> const & preds, std::vector<calc_step> & steps) {
    steps.clear();
    auto pos = p.pos();
    p.check_token_next(get_colon_tk(), "invalid 'calc' expression, ':' expected");
    if (p.curr_is_token(get_lcurly_tk())) {
        p.next();
        environment const & env = p.env();
        expr pr = p.parse_expr();
        p.check_token_next(get_rcurly_tk(), "invalid 'calc' expression, '}' expected");
        for (auto const & pred : preds) {
            if (auto refl_it = get_refl_extra_info(env, pred_op(pred))) {
                if (auto subst_it = get_subst_extra_info(env, pred_op(pred))) {
                    expr refl     = mk_op_fn(p, refl_it->m_name, refl_it->m_num_args-1, pos);
                    expr refl_pr  = p.mk_app(refl, pred_lhs(pred), pos);
                    expr subst    = mk_op_fn(p, subst_it->m_name, subst_it->m_num_args-2, pos);
                    expr subst_pr = p.mk_app({subst, pr, refl_pr}, pos);
                    steps.emplace_back(pred, subst_pr);
                }
            }
        }
        if (steps.empty())
            throw parser_error("invalid 'calc' expression, reflexivity and/or substitution rule is not defined for operator", pos);
     } else {
        expr pr = p.parse_expr();
        for (auto const & pred : preds)
            steps.emplace_back(pred, mk_calc_annotation(pr));
    }
}

/** \brief Collect distinct rhs's */
static void collect_rhss(std::vector<calc_step> const & steps, buffer<expr> & rhss) {
    rhss.clear();
    for (auto const & step : steps) {
        calc_pred const & pred = step_pred(step);
        expr const & rhs  = pred_rhs(pred);
        if (std::find(rhss.begin(), rhss.end(), rhs) == rhss.end())
            rhss.push_back(rhs);
    }
    lean_assert(!rhss.empty());
}

static unsigned get_arity_of(parser & p, name const & op) {
    return get_arity(p.env().get(op).get_type());
}

static void join(parser & p, std::vector<calc_step> const & steps1, std::vector<calc_step> const & steps2,
                 std::vector<calc_step> & res_steps, pos_info const & pos) {
    environment const & env = p.env();
    res_steps.clear();
    for (calc_step const & s1 : steps1) {
        check_interrupted();
        calc_pred const & pred1 = step_pred(s1);
        expr const & pr1        = step_proof(s1);
        for (calc_step const & s2 : steps2) {
            calc_pred const & pred2 = step_pred(s2);
            expr const & pr2        = step_proof(s2);
            if (!is_eqp(pred_rhs(pred1), pred_lhs(pred2)))
                continue;
            auto trans_it = get_trans_extra_info(env, pred_op(pred1), pred_op(pred2));
            if (trans_it) {
                expr trans    = mk_op_fn(p, trans_it->m_name, trans_it->m_num_args-5, pos);
                expr trans_pr = p.mk_app({trans, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), pr1, pr2}, pos);
                res_steps.emplace_back(calc_pred(trans_it->m_res_relation, pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
            } else if (pred_op(pred1) == get_eq_name()) {
                expr trans_right = mk_op_fn(p, get_trans_rel_right_name(), 1, pos);
                expr R           = mk_op_fn(p, pred_op(pred2), get_arity_of(p, pred_op(pred2))-2, pos);
                expr trans_pr    = p.mk_app({trans_right, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), R, pr1, pr2}, pos);
                res_steps.emplace_back(calc_pred(pred_op(pred2), pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
            } else if (pred_op(pred2) == get_eq_name()) {
                expr trans_left = mk_op_fn(p, get_trans_rel_left_name(), 1, pos);
                expr R          = mk_op_fn(p, pred_op(pred1), get_arity_of(p, pred_op(pred1))-2, pos);
                expr trans_pr   = p.mk_app({trans_left, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), R, pr1, pr2}, pos);
                res_steps.emplace_back(calc_pred(pred_op(pred1), pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
            }
        }
    }
}

static expr mk_implies(parser & p, expr const & lhs, expr const & rhs, pos_info const & pos) {
    return p.mk_app(p.mk_app(p.save_pos(mk_constant(get_implies_name()), pos), lhs, pos), rhs, pos);
}

expr parse_calc(parser & p) {
    buffer<calc_pred> preds, new_preds;
    buffer<expr>      rhss;
    std::vector<calc_step> steps, new_steps, next_steps;
    auto pos             = p.pos();
    bool is_std          = is_standard(p.env());
    expr first_pred      = p.parse_expr();
    if (is_std && is_arrow(first_pred))
        first_pred = mk_implies(p, binding_domain(first_pred), binding_body(first_pred), pos);
    decode_expr(first_pred, preds, pos);
    parse_calc_proof(p, preds, steps);
    bool single    = true; // true if calc has only one step
    expr dummy     = mk_expr_placeholder();
    while (p.curr_is_token(get_ellipsis_tk())) {
        single = false;
        pos    = p.pos();
        p.next();
        expr next_pred;
        if (is_std && p.curr_is_token(get_arrow_tk())) {
            p.next();
            expr rhs  = p.parse_expr();
            next_pred = mk_implies(p, dummy, rhs, pos);
        } else {
            next_pred = p.parse_led(dummy);
        }
        decode_expr(next_pred, preds, pos);
        collect_rhss(steps, rhss);
        new_steps.clear();
        for (auto const & pred : preds) {
            if (is_eqp(pred_lhs(pred), dummy)) {
                for (expr const & rhs : rhss)
                    new_preds.emplace_back(pred_op(pred), rhs, pred_rhs(pred));
            }
        }
        if (new_preds.empty())
            throw parser_error("invalid 'calc' expression, invalid expression", pos);
        parse_calc_proof(p, new_preds, new_steps);
        join(p, steps, new_steps, next_steps, pos);
        if (next_steps.empty())
            throw parser_error("invalid 'calc' expression, transitivity rule is not defined for current step", pos);
        steps.swap(next_steps);
    }
    buffer<expr> choices;
    for (auto const & s : steps) {
        if (single) {
            expr new_s = p.save_pos(mk_typed_expr(first_pred, step_proof(s)), pos);
            choices.push_back(new_s);
        } else {
            choices.push_back(step_proof(s));
        }
    }
    return p.save_pos(mk_choice(choices.size(), choices.data()), pos);
}

void initialize_calc() {
    g_calc_name = new name("calc");
    register_annotation(*g_calc_name);
}
void finalize_calc() {
    delete g_calc_name;
}
}
