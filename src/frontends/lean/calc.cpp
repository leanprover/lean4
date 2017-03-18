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
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
static name * g_calc_name  = nullptr;

static expr mk_calc_annotation_core(expr const & e) { return mk_annotation(*g_calc_name, e); }
static expr mk_calc_annotation(expr const & pr) {
    if (/* is_by(pr) || is_begin_end_annotation(pr) || */ is_sorry(pr)) {
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

// Check whether e is of the form (f ...) where f is a constant. If it is return f.
static calc_pred decode_expr(expr const & e, pos_info const & pos) {
    if (is_choice(e)) {
        throw parser_error("invalid 'calc' expression, overloaded expressions are not supported", pos);
    } else {
        buffer<expr> args;
        expr const & fn = get_nested_annotation_arg(get_app_args(e, args));
        unsigned nargs  = args.size();
        if (!is_constant(fn) || nargs < 2) {
            throw parser_error("invalid 'calc' expression, expression must be a function application 'f a_1 ... a_k' "
                               "where f is a constant, and k >= 2", pos);
        }
        return calc_pred(const_name(fn), args[nargs-2], args[nargs-1]);
    }
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

static calc_step parse_calc_proof(parser & p, calc_pred const & pred) {
    p.check_token_next(get_colon_tk(), "invalid 'calc' expression, ':' expected");
    auto pos = p.pos();
    expr pr  = p.parse_expr();
    return calc_step(pred, p.save_pos(mk_calc_annotation(pr), pos));
}

static unsigned get_arity_of(parser & p, name const & op) {
    return get_arity(p.env().get(op).get_type());
}

static calc_step join(parser & p, calc_step const & s1, calc_step const & s2, pos_info const & pos) {
    environment const & env = p.env();
    calc_pred const & pred1 = step_pred(s1);
    expr const & fst        = step_proof(s1);
    calc_pred const & pred2 = step_pred(s2);
    expr const & snd        = step_proof(s2);
    auto trans_it = get_trans_extra_info(env, pred_op(pred1), pred_op(pred2));
    if (trans_it) {
        expr trans    = mk_op_fn(p, trans_it->m_name, trans_it->m_num_args-5, pos);
        expr trans_pr = p.mk_app({trans, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), fst, snd}, pos);
        return calc_step(calc_pred(trans_it->m_res_relation, pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
    } else if (pred_op(pred1) == get_eq_name()) {
        expr trans_right = mk_op_fn(p, get_trans_rel_right_name(), 1, pos);
        expr R           = mk_op_fn(p, pred_op(pred2), get_arity_of(p, pred_op(pred2))-2, pos);
        expr trans_pr    = p.mk_app({trans_right, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), R, fst, snd}, pos);
        return calc_step(calc_pred(pred_op(pred2), pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
    } else if (pred_op(pred2) == get_eq_name()) {
        expr trans_left = mk_op_fn(p, get_trans_rel_left_name(), 1, pos);
        expr R          = mk_op_fn(p, pred_op(pred1), get_arity_of(p, pred_op(pred1))-2, pos);
        expr trans_pr   = p.mk_app({trans_left, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), R, fst, snd}, pos);
        return calc_step(calc_pred(pred_op(pred1), pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
    } else {
        throw parser_error("invalid 'calc' expression, transitivity rule is not defined for current step", pos);
    }
}

static expr mk_implies(parser & p, expr const & lhs, expr const & rhs, pos_info const & pos) {
    return p.mk_app(p.mk_app(p.save_pos(mk_constant(get_implies_name()), pos), lhs, pos), rhs, pos);
}

static expr parse_pred(parser & p) {
    auto pos       = p.pos();
    expr pred      = p.parse_expr();
    if (is_arrow(pred))
        return mk_implies(p, binding_domain(pred), binding_body(pred), pos);
    else
        return pred;
}

static expr parse_next_pred(parser & p, expr const & dummy) {
    auto pos       = p.pos();
    if (p.curr_is_token(get_arrow_tk())) {
        p.next();
        expr rhs  = p.parse_expr();
        return mk_implies(p, dummy, rhs, pos);
    } else {
        return p.parse_led(dummy);
    }
}

expr parse_calc(parser & p) {
    auto pos = p.pos();
    expr first_pred_expr = parse_pred(p);
    calc_pred pred       = decode_expr(first_pred_expr, pos);
    calc_step step       = parse_calc_proof(p, pred);
    bool single          = true; // true if calc has only one step
    expr dummy;

    while (p.curr_is_token(get_ellipsis_tk())) {
        single = false;
        pos    = p.pos();
        p.next();
        expr new_pred_expr = parse_next_pred(p, dummy);
        calc_pred new_pred = decode_expr(new_pred_expr, pos);
        new_pred           = calc_pred(pred_op(new_pred), pred_rhs(pred), pred_rhs(new_pred));
        calc_step new_step = parse_calc_proof(p, new_pred);
        step               = join(p, step, new_step, pos);
    }

    if (single) {
        return p.save_pos(mk_typed_expr(first_pred_expr, step_proof(step)), pos);
    } else {
        return step_proof(step);
    }
}

void initialize_calc() {
    g_calc_name = new name("calc");
    register_annotation(*g_calc_name);
}
void finalize_calc() {
    delete g_calc_name;
}
}
