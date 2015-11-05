/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/

#include "library/norm_num.h"
#include "library/constants.h"

namespace lean {
static name * g_add           = nullptr,
    * g_add1          = nullptr,
    * g_mul           = nullptr,
    * g_sub           = nullptr,
    * g_neg           = nullptr,
    * g_div           = nullptr,
    * g_bit0_add_bit0 = nullptr,
    * g_bit1_add_bit0 = nullptr,
    * g_bit0_add_bit1 = nullptr,
    * g_bit1_add_bit1 = nullptr,
    * g_bin_add_0     = nullptr,
    * g_bin_0_add     = nullptr,
    * g_bin_add_1     = nullptr,
    * g_1_add_bit0    = nullptr,
    * g_bit0_add_1    = nullptr,
    * g_bit1_add_1    = nullptr,
    * g_1_add_bit1    = nullptr,
    * g_one_add_one   = nullptr,
    * g_add1_bit0     = nullptr,
    * g_add1_bit1     = nullptr,
    * g_add1_zero     = nullptr,
    * g_add1_one      = nullptr,
    * g_subst_sum     = nullptr,
    * g_subst_subtr   = nullptr,
    * g_subst_prod    = nullptr,
    * g_mk_cong       = nullptr,
    * g_mk_eq         = nullptr,
    * g_mul_zero      = nullptr,
    * g_zero_mul      = nullptr,
    * g_mul_one       = nullptr,
    * g_mul_bit0      = nullptr,
    * g_mul_bit1      = nullptr,
    * g_has_mul       = nullptr,
    * g_add_monoid    = nullptr,
    * g_monoid        = nullptr,
    * g_ring          = nullptr,
    * g_add_comm      = nullptr,
    * g_add_group     = nullptr,
    * g_mul_zero_class = nullptr,
    * g_distrib       = nullptr,
    * g_has_neg       = nullptr,
    * g_has_sub       = nullptr,
    * g_has_div       = nullptr,
    * g_semiring      = nullptr,
    * g_eq_neg_of_add_eq_zero = nullptr,
    * g_neg_add_neg_eq = nullptr,
    * g_neg_add_pos1   = nullptr,
    * g_neg_add_pos2   = nullptr,
    * g_pos_add_neg  = nullptr,
    * g_pos_add_pos   = nullptr,
    * g_neg_mul_neg    = nullptr,
    * g_pos_mul_neg    = nullptr,
    * g_neg_mul_pos    = nullptr,
    * g_sub_eq_add_neg = nullptr,
    * g_neg_neg        = nullptr,
    * g_div_add        = nullptr,
    * g_add_div        = nullptr,
    * g_lin_ord_ring   = nullptr,
    * g_lin_ord_semiring   = nullptr,
    * g_wk_order       = nullptr,
    * g_bit0_nonneg = nullptr,
    * g_bit1_nonneg = nullptr,
    * g_zero_le_one = nullptr,
    * g_le_refl = nullptr,
    * g_bit0_pos = nullptr,
    * g_bit1_pos = nullptr,
    * g_zero_lt_one = nullptr,
    * g_field = nullptr,
    * g_nonzero_neg = nullptr,
    * g_nonzero_pos = nullptr,
    * g_div_mul = nullptr,
    * g_mul_div = nullptr,
    * g_div_helper = nullptr,
    * g_div_eq_div_helper = nullptr,
    * g_subst_div = nullptr,
    * g_nonzero_div = nullptr,
    * g_add_comm_group = nullptr;

static bool is_numeral_aux(expr const & e, bool is_first) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (!is_constant(f)) {
      return false;
    }
    if (const_name(f) == get_one_name()) {
        return args.size() == 2;
    } else if (const_name(f) == get_zero_name()) {
        return is_first && args.size() == 2;
    } else if (const_name(f) == get_bit0_name()) {
        return args.size() == 3 && is_numeral_aux(args[2], false);
    } else if (const_name(f) == get_bit1_name()) {
        return args.size() == 4 && is_numeral_aux(args[3], false);
    }
    return false;
}

bool norm_num_context::is_numeral(expr const & e) const {
    return is_numeral_aux(e, true);
}

bool norm_num_context::is_neg_app(expr const & e) const {
    return is_const_app(e, *g_neg, 3);
}

bool norm_num_context::is_div(expr const & e) const {
    return is_const_app(e, *g_div, 4);
}

/*
Takes A : Type, and tries to synthesize has_add A.
*/
expr norm_num_context::mk_has_add(expr const & e) {
    expr t = mk_app(mk_constant(get_has_add_name(), m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_add instance");
    }
}

expr norm_num_context::mk_has_mul(expr const & e) {
    expr t = mk_app(mk_constant(*g_has_mul, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_mul instance");
    }
}

expr norm_num_context::mk_has_one(expr const & e) {
    expr t = mk_app(mk_constant(get_has_one_name(), m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_one instance");
    }
}

expr norm_num_context::mk_has_zero(expr const & e) {
    expr t = mk_app(mk_constant(get_has_zero_name(), m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_one instance");
    }
}

expr norm_num_context::mk_add_monoid(expr const & e) {
    expr t = mk_app(mk_constant(*g_add_monoid, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_monoid instance");
    }
}

expr norm_num_context::mk_monoid(expr const & e) {
    expr t = mk_app(mk_constant(*g_monoid, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize monoid instance");
    }
}

expr norm_num_context::mk_field(expr const & e) {
    expr t = mk_app(mk_constant(*g_field, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize field instance");
    }
}

expr norm_num_context::mk_add_comm(expr const & e) {
    expr t = mk_app(mk_constant(*g_add_comm, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_comm_semigroup instance");
    }
}

expr norm_num_context::mk_add_group(expr const & e) {
    expr t = mk_app(mk_constant(*g_add_group, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_comm_semigroup instance");
    }
}

expr norm_num_context::mk_has_distrib(expr const & e) {
    expr t = mk_app(mk_constant(*g_distrib, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_distrib instance");
    }
}

expr norm_num_context::mk_mul_zero_class(expr const & e) {
    expr t = mk_app(mk_constant(*g_mul_zero_class, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize mul_zero instance");
    }
}

expr norm_num_context::mk_semiring(expr const & e) {
    expr t = mk_app(mk_constant(*g_semiring, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize semiring instance");
    }
}

expr norm_num_context::mk_has_neg(expr const & e) {
    expr t = mk_app(mk_constant(*g_has_neg, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_neg instance");
    }
}

expr norm_num_context::mk_has_sub(expr const & e) {
    expr t = mk_app(mk_constant(*g_has_sub, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_sub instance");
    }
}

expr norm_num_context::mk_has_div(expr const & e) {
    expr t = mk_app(mk_constant(*g_has_div, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_div instance");
    }
}

expr norm_num_context::mk_add_comm_group(expr const & e) {
    expr t = mk_app(mk_constant(*g_add_comm_group, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_comm_group instance");
    }
}

expr norm_num_context::mk_ring(expr const & e) {
    expr t = mk_app(mk_constant(*g_ring, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize ring instance");
    }
}

expr norm_num_context::mk_lin_ord_ring(expr const & e) {
    expr t = mk_app(mk_constant(*g_lin_ord_ring, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize lin_ord_ring instance");
    }
}

expr norm_num_context::mk_lin_ord_semiring(expr const & e) {
    expr t = mk_app(mk_constant(*g_lin_ord_semiring, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize lin_ord_semiring instance");
    }
}

expr norm_num_context::mk_wk_order(expr const & e) {
    expr t = mk_app(mk_constant(*g_wk_order, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize weak_order instance");
    }
}

expr norm_num_context::mk_const(name const & n) {
    return mk_constant(n, m_lvls);
}

expr norm_num_context::mk_cong(expr const & op, expr const & type, expr const & a, expr const & b, expr const & eq) {
    return mk_app({mk_const(*g_mk_cong), type, op, a, b, eq});
}

// returns <t, p> such that p is a proof that lhs + rhs = t.
pair<expr, expr> norm_num_context::mk_norm_add(expr const & lhs, expr const & rhs) {
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_lhs[0];
    auto typec = args_lhs[1];
    // std::cout << "typec in mk_norm_add is: " << typec << ". lhs: " << lhs << ", rhs: " << rhs << "\n";
    expr rv;
    expr prf;
    if (is_bit0(lhs) && is_bit0(rhs)) { // typec is has_add
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
        rv = mk_app(lhs_head, type, typec, p.first);
        prf = mk_app({mk_const(*g_bit0_add_bit0), type, mk_add_comm(type), args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit0(lhs) && is_bit1(rhs)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[3]);
        rv = mk_app({rhs_head, type, args_rhs[1], args_rhs[2], p.first});
        prf = mk_app({mk_const(*g_bit0_add_bit1), type, mk_add_comm(type), args_rhs[1], args_lhs[2], args_rhs[3], p.first, p.second});
    } else if (is_bit0(lhs) && is_one(rhs)) {
        rv = mk_app({mk_const(get_bit1_name()), type, args_rhs[1], args_lhs[1], args_lhs[2]});
        prf = mk_app({mk_const(*g_bit0_add_1), type, typec, args_rhs[1], args_lhs[2]});
    } else if (is_bit1(lhs) && is_bit0(rhs)) { // typec is has_one
        auto p = mk_norm_add(args_lhs[3], args_rhs[2]);
        rv = mk_app(lhs_head, type, typec, args_lhs[2], p.first);
        prf = mk_app({mk_const(*g_bit1_add_bit0), type, mk_add_comm(type), typec, args_lhs[3], args_rhs[2], p.first, p.second});
    } else if (is_bit1(lhs) && is_bit1(rhs)) { // typec is has_one
        auto add_ts = mk_norm_add(args_lhs[3], args_rhs[3]);
        expr add1 = mk_app({mk_const(*g_add1), type, args_lhs[2], typec, add_ts.first});
        auto p = mk_norm_add1(add1);
        rv = mk_app({mk_const(get_bit0_name()), type, args_lhs[2], p.first});
        prf = mk_app({mk_const(*g_bit1_add_bit1), type, mk_add_comm(type), typec, args_lhs[3], args_rhs[3], add_ts.first, p.first, add_ts.second, p.second});
    } else if (is_bit1(lhs) && is_one(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(*g_add1), type, args_lhs[2], typec, lhs});
        auto p = mk_norm_add1(add1);
        rv = p.first;
        prf = mk_app({mk_const(*g_bit1_add_1), type, args_lhs[2], typec, args_lhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_bit0(rhs)) { // typec is has_one
        rv = mk_app({mk_const(get_bit1_name()), type, typec, args_rhs[1], args_rhs[2]});
        prf = mk_app({mk_const(*g_1_add_bit0), type, mk_add_comm(type), typec, args_rhs[2]});
    } else if (is_one(lhs) && is_bit1(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(*g_add1), type, args_rhs[2], args_rhs[1], rhs});
        auto p = mk_norm_add1(add1);
        rv = p.first;
        prf = mk_app({mk_const(*g_1_add_bit1), type, mk_add_comm(type), typec, args_rhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_one(rhs)) {
      rv = mk_app({mk_const(get_bit0_name()), type, mk_has_add(type), lhs});
        prf = mk_app({mk_const(*g_one_add_one), type, mk_has_add(type), typec});
    } else if (is_zero(lhs)) {
        rv = rhs;
        prf = mk_app({mk_const(*g_bin_0_add), type, mk_add_monoid(type), rhs});
    } else if (is_zero(rhs)) {
        rv = lhs;
        prf = mk_app({mk_const(*g_bin_add_0), type, mk_add_monoid(type), lhs});
    } else {
        std::cout << "\n\n bad args: " << lhs_head << ", " << rhs_head << "\n";
        std::cout << "\nlhs: " << lhs;
        std::cout << "\nrhs: " << rhs;
      throw exception("mk_norm_add got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_add1(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr p = args[3];
    buffer<expr> ne_args;
    expr ne = get_app_args(p, ne_args);
    expr rv;
    expr prf;
    // args[1] = has_add, args[2] = has_one
    if (is_bit0(p)) {
        auto has_one = args[2];
        rv = mk_app({mk_const(get_bit1_name()), args[0], args[2], args[1], ne_args[2]});
        prf = mk_app({mk_const(*g_add1_bit0), args[0], args[1], args[2], ne_args[2]});
    } else if (is_bit1(p)) { // ne_args : has_one, has_add
        auto np = mk_norm_add1(mk_app({mk_const(*g_add1), args[0], args[1], args[2], ne_args[3]}));
        rv = mk_app({mk_const(get_bit0_name()), args[0], args[1], np.first});
        prf = mk_app({mk_const(*g_add1_bit1), args[0], mk_add_comm(args[0]), args[2], ne_args[3], np.first, np.second});
    } else if (is_zero(p)) {
        rv = mk_app({mk_const(get_one_name()), args[0], args[2]});
        prf = mk_app({mk_const(*g_add1_zero), args[0], mk_add_monoid(args[0]), args[2]});
    } else if (is_one(p)) {
        rv = mk_app({mk_const(get_bit0_name()), args[0], args[1], mk_app({mk_const(get_one_name()), args[0], args[2]})});
        prf = mk_app({mk_const(*g_add1_one), args[0], args[1], args[2]});
    } else {
        std::cout << "malformed add1: " << ne << "\n";
        throw exception("malformed add1");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_mul(expr const & lhs, expr const & rhs) {
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_rhs[0];
    auto typec = args_rhs[1];
    expr rv;
    expr prf;
    if (is_zero(rhs)) {
        rv = rhs;
        prf = mk_app({mk_const(*g_mul_zero), type, mk_mul_zero_class(type), lhs});
    } else if (is_zero(lhs)) {
        rv = lhs;
        prf = mk_app({mk_const(*g_zero_mul), type, mk_mul_zero_class(type), rhs});
    } else if (is_one(rhs)) {
        rv = lhs;
        prf = mk_app({mk_const(*g_mul_one), type, mk_monoid(type), lhs});
    } else if (is_bit0(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[2]);
        rv = mk_app({rhs_head, type, typec, mtp.first});
        prf = mk_app({mk_const(*g_mul_bit0), type, mk_has_distrib(type), lhs, args_rhs[2], mtp.first, mtp.second});
    } else if (is_bit1(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[3]);
        // std::cout << "** in mk_norm_mul. calling mk_norm_add on" << mtp.first << ", " << lhs;
        auto atp = mk_norm_add(mk_app({mk_const(get_bit0_name()), type, args_rhs[2], mtp.first}), lhs);
        rv = atp.first;
        prf = mk_app({mk_const(*g_mul_bit1), type, mk_semiring(type), lhs, args_rhs[3],
              mtp.first, atp.first, mtp.second, atp.second});
    } else {
      std::cout << "bad args to mk_norm_mul: " << rhs << "\n";
      throw exception("mk_norm_mul got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_div(expr const &, expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_div");
}

pair<expr, expr> norm_num_context::mk_norm_sub(expr const &, expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet -- mk_norm_sub");
}

optional<mpq> norm_num_context::to_mpq(expr const & e) {
    auto v = to_num(e);
    if (v) {
        return optional<mpq>(mpq(*v));
    } else {
        return optional<mpq>();
    }
}

mpq norm_num_context:: mpq_of_expr(expr const & e){
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f)) {
        throw exception("cannot find num of nonconstant");
    } else if (const_name(f) == *g_add && args.size() == 4) {
        return mpq_of_expr(args[2]) + mpq_of_expr(args[3]);
    } else if (const_name(f) == *g_mul && args.size() == 4) {
        return mpq_of_expr(args[2]) * mpq_of_expr(args[3]);
    } else if (const_name(f) == *g_sub && args.size() == 4) {
        return mpq_of_expr(args[2]) - mpq_of_expr(args[3]);
    } else if (const_name(f) == *g_div && args.size() == 4) {
        mpq num = mpq_of_expr(args[2]), den = mpq_of_expr(args[3]);
        if (den != 0)
            return mpq_of_expr(args[2]) / mpq_of_expr(args[3]);
        else
            throw exception("divide by 0");
    } else if (const_name(f) == *g_neg && args.size() == 3) {
        return neg(mpq_of_expr(args[2]));
    } else {
        auto v = to_mpq(e);
        if (v) {
            return *v;
        } else {
            std::cout << "error : " << f << args.size() << "\n";
            throw exception("expression in mpq_of_expr is malfomed");
        }
    }
}

mpz norm_num_context::num_of_expr(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f)) {
        throw exception("cannot find num of nonconstant");
    }
    auto v = to_num(e);
    if (v) {
        return *v;
    }
    if (const_name(f) == *g_add && args.size() == 4) {
        return num_of_expr(args[2]) + num_of_expr(args[3]);
    } else if (const_name(f) == *g_mul && args.size() == 4) {
        return num_of_expr(args[2]) * num_of_expr(args[3]);
    } else if (const_name(f) == *g_sub && args.size() == 4) {
        return num_of_expr(args[2]) - num_of_expr(args[3]);
    } else if (const_name(f) == *g_neg && args.size() == 3) {
        return neg(num_of_expr(args[2]));
    } else {
        std::cout << "error : " << f << "\n";
        throw exception("expression in num_of_expr is malfomed");
    }
}

pair<expr, expr> norm_num_context::get_type_and_arg_of_neg(expr & e) {
    lean_assert(is_neg_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    return pair<expr, expr>(args[0], args[2]);
}

// returns a proof that s_lhs + s_rhs = rhs, where all are negated numerals
expr norm_num_context::mk_norm_eq_neg_add_neg(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    auto s_rhs_v = get_type_and_arg_of_neg(s_rhs).second;
    auto rhs_v = get_type_and_arg_of_neg(rhs);
    expr type = rhs_v.first;
    auto sum_pr = mk_norm_eq_pos_add_pos(s_lhs_v, s_rhs_v, rhs_v.second);
    return mk_app({mk_const(*g_neg_add_neg_eq), type, mk_add_comm_group(type), s_lhs_v, s_rhs_v, rhs_v.second, sum_pr});
}

expr norm_num_context::mk_norm_eq_neg_add_pos(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs);
    expr type = s_lhs_v.first;
    if (is_neg_app(rhs)) {
        auto rhs_v = get_type_and_arg_of_neg(rhs).second;
        auto sum_pr = mk_norm_eq_pos_add_pos(s_rhs, rhs_v, s_lhs_v.second);
        return mk_app({mk_const(*g_neg_add_pos1), type, mk_add_comm_group(type), s_lhs_v.second, s_rhs, rhs_v, sum_pr});
    } else {
        auto sum_pr = mk_norm_eq_pos_add_pos(s_lhs_v.second, rhs, s_rhs);
        return mk_app({mk_const(*g_neg_add_pos2), type, mk_add_comm_group(type), s_lhs_v.second, s_rhs, rhs, sum_pr});
    }
}

expr norm_num_context::mk_norm_eq_pos_add_neg(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg_app(s_rhs));
    lean_assert(!is_neg_app(s_lhs));
    expr prf = mk_norm_eq_neg_add_pos(s_rhs, s_lhs, rhs);
    expr type = get_type_and_arg_of_neg(s_rhs).first;
    return mk_app({mk_const(*g_pos_add_neg), type, mk_add_comm_group(type), s_lhs, s_rhs, rhs, prf});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_add_pos(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto p = mk_norm_add(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}

expr norm_num_context::mk_norm_eq_neg_mul_neg(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    expr s_rhs_v, type;
    std::tie(type, s_rhs_v) = get_type_and_arg_of_neg(s_rhs);
    auto prod_pr = mk_norm(mk_mul(type, s_lhs_v, s_rhs_v)); //, rhs);
    lean_assert(to_num(rhs) == to_num(prod_pr.first));
    return mk_app({mk_const(*g_neg_mul_neg), type, mk_ring(type), s_lhs_v, s_rhs_v, rhs, prod_pr.second});
}

expr norm_num_context::mk_norm_eq_neg_mul_pos(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    expr s_lhs_v, type;
    std::tie(type, s_lhs_v) = get_type_and_arg_of_neg(s_lhs);
    auto rhs_v = get_type_and_arg_of_neg(rhs).second;
    auto prod_pr = mk_norm(mk_mul(type, s_lhs_v, s_rhs)); //, rhs_v);
    return mk_app({mk_const(*g_neg_mul_pos), type, mk_ring(type), s_lhs_v, s_rhs, rhs_v, prod_pr.second});
}

expr norm_num_context::mk_norm_eq_pos_mul_neg(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    expr s_rhs_v, type;
    std::tie(type, s_rhs_v) = get_type_and_arg_of_neg(s_rhs);
    auto rhs_v = get_type_and_arg_of_neg(rhs).second;
    auto prod_pr = mk_norm(mk_mul(type, s_lhs, s_rhs_v)); //, rhs_v);
    return mk_app({mk_const(*g_pos_mul_neg), type, mk_ring(type), s_lhs, s_rhs_v, rhs_v, prod_pr.second});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_mul_pos(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto p = mk_norm_mul(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}

expr norm_num_context::from_pos_num(mpz const & n, expr const & type) {
    lean_assert(n > 0);
    if (n == 1)
        return mk_app({mk_const(get_one_name()), type, mk_has_one(type)});
    if (n % mpz(2) == 1)
        return mk_app({mk_const(get_bit1_name()), type, mk_has_one(type), mk_has_add(type), from_pos_num(n/2, type)});
    else
        return mk_app({mk_const(get_bit0_name()), type, mk_has_add(type), from_pos_num(n/2, type)});
}

expr norm_num_context::from_num(mpz const & n, expr const & type) {
    expr r;
    lean_assert(n >= 0);
    if (n == 0)
        r = mk_app(mk_const(get_zero_name()), type, mk_has_zero(type));
    else
        r = from_pos_num(n, type);
    lean_assert(*to_num(r) == n);
    return r;
}

// assumes q >= 0
expr norm_num_context::from_mpq(mpq const & q, expr const & type) {
    mpz numer = q.get_numerator();
    mpz denom = q.get_denominator();
    lean_assert(numer >= 0 && denom >= 0);
    if (denom == 1) {
        return from_num(numer, type);
    } else {
        return mk_div(type, from_num(numer, type), from_num(denom, type));
    }
}

expr norm_num_context::mk_div(expr const & type, expr const & e1, expr const & e2) {
    auto has_div = mk_has_div(type);
    return mk_app({mk_const(*g_div), type, has_div, e1, e2});
}

expr norm_num_context::mk_neg(expr const & type, expr const & e) {
    auto has_neg = mk_has_neg(type);
    return mk_app({mk_const(*g_neg), type, has_neg, e});
}

expr norm_num_context::mk_add(expr const & type, expr const & e1, expr const & e2) {
    auto has_add = mk_has_add(type);
    return mk_app({mk_const(*g_add), type, has_add, e1, e2});
}

expr norm_num_context::mk_mul(expr const & type, expr const & e1, expr const & e2) {
    auto has_mul = mk_has_mul(type);
    return mk_app({mk_const(*g_mul), type, has_mul, e1, e2});
}

/*mpz mpz_gcd(mpz a, mpz b) {
    return b == 0 ? a : mpz_gcd(b, a % b);
}*/

/*pair<expr, expr> norm_num_context::mk_norm_div_over_div(expr & lhs, expr & rhs) {

    buffer<expr> lhs_args, rhs_args;
    get_app_args(lhs, lhs_args);
    get_app_args(rhs, rhs_args);
    expr type = lhs_args[0];
    expr a = lhs_args[2], b = lhs_args[3], c = rhs_args[2], d = rhs_args[3];
    lean_assert(!is_div(a) && !is_div(b) && !is_div(c) && !is_div(d));
    // normalizing (a/b) / (c/d), where a, b, c, d are not divs
    auto nlhs = mk_norm(mk_mul(type, a, d));
    auto nrhs = mk_norm(mk_mul(type, b, c));
    auto nlhs_val = to_num(nlhs.first), rlhs_val = to_num(nrhs.first);
    if (nlhs_val && rlhs_val) {

    }
}

pair<expr, expr> norm_num_context::mk_norm_div_over_num(expr &, expr &) {
}

pair<expr, expr> norm_num_context::mk_norm_num_over_div(expr &, expr &) {

}

pair<expr, expr> norm_num_context::mk_norm_num_over_num(expr &, expr &) {

}*/

// s_lhs is div. returns proof that s_lhs + s_rhs = rhs
expr norm_num_context::mk_norm_div_add(expr & s_lhs, expr & s_rhs, expr & rhs) {
    buffer<expr> s_lhs_args;
    get_app_args(s_lhs, s_lhs_args);
    expr type = s_lhs_args[0];
    expr num = s_lhs_args[2], den = s_lhs_args[3];
    expr new_lhs = mk_add(type, num, mk_mul(type, s_rhs, den));
    auto npr_l = mk_norm(new_lhs);
    auto npr_r = mk_norm(mk_mul(type, rhs, den));
    lean_assert(to_mpq(npr_l.first) == to_mpq(npr_r.first));
    if (!(is_numeral(den))) { std::cout << "\n****bad input in mk_norm_div_add\n"; }
    expr den_neq_zero = mk_nonzero_prf(den);
    return mk_app({mk_const(*g_div_add), type, mk_field(type), num, den, s_rhs, rhs,
                npr_l.first, den_neq_zero, npr_l.second, npr_r.second});
}

// s_rhs is div. returns proof that s_lhs + s_rhs = rhs
expr norm_num_context::mk_norm_add_div(expr & s_lhs, expr & s_rhs, expr & rhs) {
    buffer<expr> s_rhs_args;
    get_app_args(s_rhs, s_rhs_args);
    expr type = s_rhs_args[0];
    expr num = s_rhs_args[2], den = s_rhs_args[3];
    expr new_lhs = mk_add(type, mk_mul(type, den, s_lhs), num);
    auto npr_l = mk_norm(new_lhs);
    auto npr_r = mk_norm(mk_mul(type, den, rhs));
    lean_assert(to_mpq(npr_l.first) == to_mpq(npr_r.first));
    if (!(is_numeral(den))) { std::cout << "\n****bad input in mk_norm_add_div\n"; }
    expr den_neq_zero = mk_nonzero_prf(den);
    return mk_app({mk_const(*g_add_div), type, mk_field(type), num, den, s_rhs, rhs,
                npr_l.first, den_neq_zero, npr_l.second, npr_r.second});
}

// if e is a numeral or a negation of a numeral or division, returns proof that e != 0
expr norm_num_context::mk_nonzero_prf(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (const_name(f) == *g_neg) {
        return mk_app({mk_const(*g_nonzero_neg), args[0], mk_lin_ord_ring(args[0]), args[2], mk_pos_prf(args[2])});
    } else if (const_name(f) == *g_div) {
        expr num_pr = mk_nonzero_prf(args[2]), den_pr = mk_nonzero_prf(args[3]);
        return mk_app({mk_const(*g_nonzero_div), args[0], mk_field(args[0]), args[2], args[3], num_pr, den_pr});
    } else {
        return mk_app({mk_const(*g_nonzero_pos), args[0], mk_lin_ord_semiring(args[0]), e, mk_pos_prf(e)});
    }
}

// if e is a numeral, makes a proof that e > 0
expr norm_num_context::mk_pos_prf(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    expr type = args[0];
    expr prf;
    if (is_bit0(e)) {
        prf = mk_pos_prf(args[2]);
        return mk_app({mk_const(*g_bit0_pos), type, mk_lin_ord_semiring(type), args[2], prf});
    } else if (is_bit1(e)) {
        prf = mk_nonneg_prf(args[3]);
        return mk_app({mk_const(*g_bit1_pos), type, mk_lin_ord_semiring(type), args[3], prf});
    } else if (is_one(e)) {
        return mk_app({mk_const(*g_zero_lt_one), type, mk_lin_ord_semiring(type)});
    } else {
        std::cout << "bad call to mk_pos_prf: " << e << "\n";
        throw exception("mk_pos_proof called on zero or non_numeral");
    }
}

expr norm_num_context::mk_nonneg_prf(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    expr type = args[0];
    expr prf;
    if (is_bit0(e)) {
        prf = mk_nonneg_prf(args[2]);
        return mk_app({mk_const(*g_bit0_nonneg), type, mk_lin_ord_semiring(type), args[2], prf});
    } else if (is_bit1(e)) {
        prf = mk_nonneg_prf(args[3]);
        return mk_app({mk_const(*g_bit1_nonneg), type, mk_lin_ord_semiring(type), args[3], prf});
    } else if (is_one(e)) {
        return mk_app({mk_const(*g_zero_le_one), type, mk_lin_ord_ring(type)});
    } else if (is_zero(e)) {
        return mk_app({mk_const(*g_le_refl), type, mk_wk_order(type), mk_app({mk_const(get_zero_name()), type, mk_has_zero(type)})});
    } else {
        std::cout << "bad call to mk_nonneg_prf: " << e << "\n";
        throw exception("mk_nonneg_proof called on zero or non_numeral");
    }
}

// s_lhs is div. returns proof that s_lhs * s_rhs = rhs
expr norm_num_context::mk_norm_div_mul(expr & s_lhs, expr & s_rhs, expr & rhs) {
    buffer<expr> args;
    get_app_args(s_lhs, args);
    expr type = args[0];
    expr new_num = mk_mul(type, args[2], s_rhs);
    auto prf = mk_norm(mk_div(type, new_num, args[3]));
    lean_assert(to_mpq(prf.first) == to_mpq(rhs));
    if (!(is_numeral(args[3]))) { std::cout << "\n****bad input in mk_norm_div_mul\n"; }
    expr den_ne_zero = mk_nonzero_prf(args[3]);
    return mk_app({mk_const(*g_div_mul), type, mk_field(type), args[2], args[3], s_rhs, rhs, den_ne_zero, prf.second});
}

expr norm_num_context::mk_norm_mul_div(expr & s_lhs, expr & s_rhs, expr & rhs) {
    buffer<expr> args;
    get_app_args(s_rhs, args);
    expr type = args[0];
    expr new_num = mk_mul(type, s_lhs, args[2]);
    auto prf = mk_norm(mk_div(type, new_num, args[3]));
    lean_assert(to_mpq(prf.first) == to_mpq(rhs));
    if (!(is_numeral(args[3]))) { std::cout << "\n****bad input in mk_norm_mul_div\n"; }
    expr den_ne_zero = mk_nonzero_prf(args[3]);
    return mk_app({mk_const(*g_mul_div), type, mk_field(type), s_lhs, args[2], args[3], rhs, den_ne_zero, prf.second});
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    //std::cout << "mk_norm: " << e << "\n";
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f) || args.size() == 0) {
        throw exception("malformed argument to mk_norm_expr");
    }
    m_lvls = const_levels(f);
    expr type = args[0];
    mpq val = mpq_of_expr(e);
    expr nval; // e = nval
    if (val >= 0) {
        nval = from_mpq(val, type);
    } else {
        nval = mk_neg(type, from_mpq(neg(val), type));
    }
    if (const_name(f) == *g_add && args.size() == 4) {
        expr prf;
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        if (is_div(lhs_p.first)) {
            prf = mk_norm_div_add(lhs_p.first, rhs_p.first, nval);
        } else if (is_div(rhs_p.first)) {
            prf = mk_norm_add_div(lhs_p.first, rhs_p.first, nval);
        } else if (is_neg_app(lhs_p.first)) {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_neg_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_neg_add_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_pos_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_pos_add_pos(lhs_p.first, rhs_p.first, nval);
            }
        }
        expr rprf = mk_app({mk_const(*g_subst_sum), type, mk_has_add(type), args[2], args[3],
                    lhs_p.first, rhs_p.first, nval, lhs_p.second, rhs_p.second, prf});
        return pair<expr, expr>(nval, rprf);

    } else if (const_name(f) == *g_sub && args.size() == 4) {
        expr sum = mk_add(args[0], args[2], mk_neg(args[0], args[3]));
        auto anprf = mk_norm(sum);
        expr rprf = mk_app({mk_const(*g_subst_subtr), type, mk_add_group(type), args[2], args[3], anprf.first, anprf.second});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == *g_neg  && args.size() == 3) {
        auto prf = mk_norm(args[2]);
        /*std::cout << "in mk_norm. const is neg. e: " << e << "\n";
        std::cout << " val: ";
        std::cout << val;
        std::cout << "\n nval: ";
        std::cout << nval << "\n";*/
        lean_assert(mpq_of_expr(prf.first) == neg(val));

        if (is_neg_app(nval)) {
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            expr rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2], nval_args[2], prf.second);
            // std::cout << " RETURNING: (" << nval << ", " << rprf << "\n";
            return pair<expr, expr>(nval, rprf);
        } else {
            expr rprf = mk_app({mk_const(*g_neg_neg), type, mk_add_group(type), args[2], nval, prf.second});
            return pair<expr, expr>(nval, rprf);
        }
    } else if (const_name(f) == *g_mul && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        expr prf;
        if (is_div(lhs_p.first)) {
            prf = mk_norm_div_mul(lhs_p.first, rhs_p.first, nval);
        } else if (is_div(rhs_p.first)) {
            prf = mk_norm_mul_div(lhs_p.first, rhs_p.first, nval);
        } else if (is_zero(lhs_p.first) || is_zero(rhs_p.first)) {
            prf = mk_norm_mul(lhs_p.first, rhs_p.first).second;
        } else if (is_neg_app(lhs_p.first)) {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_neg_mul_neg(lhs_p.first, rhs_p.first, nval);
            } else { // bad args passing here
                prf = mk_norm_eq_neg_mul_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_pos_mul_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_pos_mul_pos(lhs_p.first, rhs_p.first, nval);
            }
        }
        expr rprf = mk_app({mk_const(*g_subst_prod), type, mk_has_mul(args[0]), args[2], args[3],
                          lhs_p.first, rhs_p.first, nval, lhs_p.second, rhs_p.second, prf});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_division_name() && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        //std::cout << "div. lhs, rhs:" << lhs_p.first << ",\n" << rhs_p.first << ".\n";
        expr prf;
        if (is_div(nval)) {
            // std::cout << "nval is div. (" << nval << ")\n";
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            expr nval_num = nval_args[2], nval_den = nval_args[3];
            auto lhs_mul = mk_norm(mk_mul(type, lhs_p.first, nval_den));
            auto rhs_mul = mk_norm(mk_mul(type, nval_num, rhs_p.first));
            expr den_nonzero = mk_nonzero_prf(rhs_p.first);
            expr nval_den_nonzero = mk_nonzero_prf(nval_den);
            prf = mk_app({mk_const(*g_div_eq_div_helper), type, mk_field(type), lhs_p.first, rhs_p.first, nval_num, nval_den, lhs_mul.first, lhs_mul.second, rhs_mul.second, den_nonzero, nval_den_nonzero});
        } else {
            auto prod = mk_norm(mk_mul(type, nval, rhs_p.first));
            auto val1 = to_mpq(prod.first), val2 = to_mpq(lhs_p.first);
            if (val1 && val2) {
                lean_assert(*val1 == *val2);
            }
            expr den_nonzero = mk_nonzero_prf(rhs_p.first);
            prf = mk_app({mk_const(*g_div_helper), type, mk_field(type), lhs_p.first, rhs_p.first, nval, den_nonzero, prod.second});
        }
        expr rprf = mk_app({mk_const(*g_subst_div), type, mk_has_div(type), lhs_p.first, rhs_p.first, args[2], args[3], nval, prf, lhs_p.second, rhs_p.second});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_bit0_name() && args.size() == 3) {
        lean_assert(is_bit0(nval));
        buffer<expr> nval_args;
        get_app_args(nval, nval_args);
        auto prf = mk_norm(args[2]);
        auto rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2], nval_args[2], prf.second);
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_bit1_name() && args.size() == 4) {
        lean_assert(is_bit1(nval));
        buffer<expr> nval_args;
        get_app_args(nval, nval_args);
        auto prf = mk_norm(args[3]);
        auto rprf = mk_cong(mk_app(f, args[0], args[1], args[2]), type, args[3], nval_args[3], prf.second);
        return pair<expr, expr>(nval, rprf);
    } else if ((const_name(f) == get_zero_name() || const_name(f) == get_one_name()) && args.size() == 2) {
        auto p = pair<expr, expr>(e, mk_app({mk_const(*g_mk_eq), args[0], e}));
//        return pair<expr, expr>(e, mk_app({mk_const(*g_mk_eq), args[0], e}));
        return p;
    } else {
        std::cout << "error with name " << const_name(f) << " and size " << args.size() << ".\n";
        throw exception("mk_norm found unrecognized combo ");
    }
}

void initialize_norm_num() {
    g_add     = new name("add");
    g_add1    = new name("add1");
    g_mul     = new name("mul");
    g_sub     = new name("sub");
    g_neg     = new name("neg");
    g_div     = new name("division");
    g_bit0_add_bit0 = new name("bit0_add_bit0_helper");
    g_bit1_add_bit0 = new name("bit1_add_bit0_helper");
    g_bit0_add_bit1 = new name("bit0_add_bit1_helper");
    g_bit1_add_bit1 = new name("bit1_add_bit1_helper");
    g_bin_add_0     = new name("bin_add_zero");
    g_bin_0_add     = new name("bin_zero_add");
    g_bin_add_1     = new name("bin_add_one");
    g_1_add_bit0    = new name("one_add_bit0");
    g_bit0_add_1    = new name("bit0_add_one");
    g_bit1_add_1    = new name("bit1_add_one_helper");
    g_1_add_bit1    = new name("one_add_bit1_helper");
    g_one_add_one   = new name("one_add_one");
    g_add1_bit0     = new name("add1_bit0");
    g_add1_bit1     = new name("add1_bit1_helper");
    g_add1_zero     = new name("add1_zero");
    g_add1_one      = new name("add1_one");
    g_subst_sum     = new name("subst_into_sum");
    g_subst_subtr   = new name("subst_into_subtr");
    g_subst_prod    = new name("subst_into_prod");
    g_mk_cong       = new name("mk_cong");
    g_mk_eq         = new name("mk_eq");
    g_zero_mul      = new name("zero_mul");
    g_mul_zero      = new name("mul_zero");
    g_mul_one       = new name("mul_one");
    g_mul_bit0      = new name("mul_bit0_helper");
    g_mul_bit1      = new name("mul_bit1_helper");
    g_has_mul       = new name("has_mul");
    g_add_monoid        = new name("algebra", "add_monoid");
    g_ring        = new name("algebra", "ring");
    g_monoid        = new name("algebra", "monoid");
    g_add_comm      = new name("algebra", "add_comm_semigroup");
    g_add_group      = new name("algebra", "add_group");
    g_mul_zero_class      = new name("algebra", "mul_zero_class");
    g_distrib       = new name("algebra", "distrib");
    g_has_neg       = new name("has_neg"); //"algebra",
    g_has_sub       = new name("has_sub");
    g_has_div       = new name("has_division");
    g_semiring      = new name("algebra", "semiring");
    g_lin_ord_ring      = new name("algebra", "linear_ordered_ring");
    g_lin_ord_semiring      = new name("algebra", "linear_ordered_semiring");
    g_eq_neg_of_add_eq_zero = new name("algebra", "eq_neg_of_add_eq_zero");
    g_neg_add_neg_eq = new name("neg_add_neg_helper");
    g_neg_add_pos1 = new name("neg_add_pos_helper1");
    g_neg_add_pos2 = new name("neg_add_pos_helper2");
    g_pos_add_neg = new name("pos_add_neg_helper");
    g_neg_mul_neg = new name("neg_mul_neg_helper");
    g_neg_mul_pos = new name("neg_mul_pos_helper");
    g_pos_mul_neg = new name("pos_mul_neg_helper");
    g_sub_eq_add_neg = new name("sub_eq_add_neg_helper");
    g_pos_add_pos = new name("pos_add_pos_helper");
    g_neg_neg = new name("neg_neg_helper");
    g_add_comm_group = new name("algebra", "add_comm_group");
    g_add_div = new name("add_div_helper");
    g_div_add = new name("div_add_helper");
    g_bit0_nonneg = new name("nonneg_bit0_helper");
    g_bit1_nonneg = new name("nonneg_bit1_helper");
    g_zero_le_one = new name("algebra", "zero_le_one");
    g_le_refl = new name("algebra", "le.refl");
    g_bit0_pos = new name("pos_bit0_helper");
    g_bit1_pos = new name("pos_bit1_helper");
    g_zero_lt_one = new name("algebra", "zero_lt_one");
    g_wk_order = new name("algebra", "weak_order");
    g_field = new name("algebra", "field");
    g_nonzero_neg = new name("nonzero_of_neg_helper");
    g_nonzero_pos = new name("nonzero_of_pos_helper");
    g_mul_div = new name("mul_div_helper");
    g_div_mul = new name("div_mul_helper");
    g_div_helper = new name("div_helper");
    g_div_eq_div_helper = new name("div_eq_div_helper");
    g_subst_div = new name("subst_into_div");
    g_nonzero_div = new name("nonzero_of_div_helper");
}

void finalize_norm_num() {
    delete g_add;
    delete g_add1;
    delete g_mul;
    delete g_sub;
    delete g_neg;
    delete g_div;
    delete g_bit0_add_bit0;
    delete g_bit1_add_bit0;
    delete g_bit0_add_bit1;
    delete g_bit1_add_bit1;
    delete g_bin_add_0;
    delete g_bin_0_add;
    delete g_bin_add_1;
    delete g_1_add_bit0;
    delete g_bit0_add_1;
    delete g_bit1_add_1;
    delete g_1_add_bit1;
    delete g_one_add_one;
    delete g_add1_bit0;
    delete g_add1_bit1;
    delete g_add1_zero;
    delete g_add1_one;
    delete g_subst_sum;
    delete g_subst_subtr;
    delete g_subst_prod;
    delete g_mk_cong;
    delete g_mk_eq;
    delete g_mul_zero;
    delete g_zero_mul;
    delete g_mul_one;
    delete g_mul_bit0;
    delete g_mul_bit1;
    delete g_has_mul;
    delete g_add_monoid;
    delete g_monoid;
    delete g_ring;
    delete g_add_comm;
    delete g_add_group;
    delete g_mul_zero_class;
    delete g_distrib;
    delete g_has_neg;
    delete g_has_sub;
    delete g_has_div;
    delete g_semiring;
    delete g_eq_neg_of_add_eq_zero;
    delete g_neg_add_neg_eq;
    delete g_neg_add_pos1;
    delete g_neg_add_pos2;
    delete g_pos_add_neg;
    delete g_pos_add_pos;
    delete g_neg_mul_neg;
    delete g_neg_mul_pos;
    delete g_pos_mul_neg;
    delete g_sub_eq_add_neg;
    delete g_neg_neg;
    delete g_add_comm_group;
    delete g_div_add;
    delete g_add_div;
    delete g_bit0_nonneg;
    delete g_bit1_nonneg;
    delete g_zero_le_one;
    delete g_le_refl;
    delete g_bit0_pos;
    delete g_bit1_pos;
    delete g_zero_lt_one;
    delete g_wk_order;
    delete g_div_mul;
    delete g_div_helper;
    delete g_div_eq_div_helper;
    delete g_mul_div;
    delete g_nonzero_div;
}
}
