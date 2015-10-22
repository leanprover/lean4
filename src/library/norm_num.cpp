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
    * g_add_comm      = nullptr,
    * g_add_group     = nullptr,
    * g_mul_zero_class = nullptr,
    * g_distrib       = nullptr,
    * g_has_neg       = nullptr,
    * g_has_sub       = nullptr,
    * g_semiring      = nullptr,
    * g_eq_neg_of_add_eq_zero = nullptr,
    * g_neg_add_neg_eq = nullptr,
    * g_neg_add_pos1   = nullptr,
    * g_neg_add_pos2   = nullptr,
    * g_pos_add_neg  = nullptr,
    * g_pos_add_pos   = nullptr,
    * g_sub_eq_add_neg = nullptr,
    * g_neg_neg        = nullptr,
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
    } else if (const_name(f) == get_bit1_name() || const_name(f) == get_bit0_name()) {
        return args.size() == 3 && is_numeral_aux(args[2], false);
    }
    return false;
}

bool norm_num_context::is_numeral(expr const & e) const {
    return is_numeral_aux(e, true);
}

bool is_neg(expr const & e) {
    return is_const_app(e, *g_neg, 3);
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

expr norm_num_context::mk_add_comm_group(expr const & e) {
    expr t = mk_app(mk_constant(*g_add_comm_group, m_lvls), e);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_comm_group instance");
    }
}

expr norm_num_context::mk_const(name const & n) {
    return mk_constant(n, m_lvls);
}

expr norm_num_context::mk_cong(expr const & op, expr const & type, expr const & a, expr const & b, expr const & eq) {
    return mk_app({mk_const(*g_mk_cong), type, op, a, b, eq});
}

/*pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f)) {
        throw exception("cannot take norm of nonconstant");
    }
    m_lvls = const_levels(f);
    if (const_name(f) == *g_add && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        auto add_p = mk_norm_add(lhs_p.first, rhs_p.first);
        expr prf = mk_app({mk_const(*g_subst_sum), args[0], mk_has_add(args[0]), args[2], args[3],
                          lhs_p.first, rhs_p.first, add_p.first, lhs_p.second, rhs_p.second, add_p.second});
        return pair<expr, expr>(add_p.first, prf);
    } else if (const_name(f) == *g_mul && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        auto mul_p = mk_norm_mul(lhs_p.first, rhs_p.first);
        expr prf = mk_app({mk_const(*g_subst_prod), args[0], mk_has_mul(args[0]), args[2], args[3],
                          lhs_p.first, rhs_p.first, mul_p.first, lhs_p.second, rhs_p.second, mul_p.second});
        return pair<expr, expr>(mul_p.first, prf);
    } else if (const_name(f) == get_bit0_name()  && args.size() == 3) {
        auto arg = mk_norm(args[2]);
        expr rv = mk_app({f, args[0], args[1], arg.first});
        expr prf = mk_cong(mk_app({f, args[0], args[1]}), args[0], args[2], arg.first, arg.second);
        return pair<expr, expr>(rv, prf);
    } else if (const_name(f) == get_bit1_name() && args.size() == 4) {
        auto arg = mk_norm(args[3]);
        expr rv = mk_app({f, args[0], args[1], args[2], arg.first});
        expr prf = mk_cong(mk_app({f, args[0], args[1], args[2]}), args[0], args[3], arg.first, arg.second);
        return pair<expr, expr>(rv, prf);
    } else if ((const_name(f) == get_zero_name() || const_name(f) == get_one_name()) && args.size() == 2) {
        return pair<expr, expr>(e, mk_app({mk_const(*g_mk_eq), args[0], e}));
    } else {
        std::cout << "error with name " << const_name(f) << " and size " << args.size() << ".\n";
        throw exception("mk_norm found unrecognized combo ");
    }
    // TODO(Rob): cases for sub, div
    }*/

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

mpz norm_num_context::num_of_expr(expr const & e) { // note : mpz only supports nonneg nums
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

pair<expr, expr> get_type_and_arg_of_neg(expr & e) {
    lean_assert(is_neg(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    return pair<expr, expr>(args[0], args[2]);
}

// returns a proof that s_lhs + s_rhs = rhs, where all are negated numerals
expr norm_num_context::mk_norm_eq_neg_add_neg(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg(s_lhs));
    lean_assert(is_neg(s_rhs));
    lean_assert(is_neg(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    auto s_rhs_v = get_type_and_arg_of_neg(s_rhs).second;
    auto rhs_v = get_type_and_arg_of_neg(rhs);
    expr type = rhs_v.first;
    auto sum_pr = mk_norm_eq_pos_add_pos(s_lhs_v, s_rhs_v, rhs_v.second);
    return mk_app({mk_const(*g_neg_add_neg_eq), type, mk_add_comm_group(type), s_lhs_v, s_rhs_v, rhs_v.second, sum_pr});
}

expr norm_num_context::mk_norm_eq_neg_add_pos(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(is_neg(s_lhs));
    lean_assert(!is_neg(s_rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs);
    expr type = s_lhs_v.first;
    if (is_neg(rhs)) {
        auto rhs_v = get_type_and_arg_of_neg(rhs).second;
        auto sum_pr = mk_norm_eq_pos_add_pos(s_rhs, rhs_v, s_lhs_v.second);
        return mk_app({mk_const(*g_neg_add_pos1), type, mk_add_comm_group(type), s_lhs_v.second, s_rhs, rhs_v, sum_pr});
    } else {
        auto sum_pr = mk_norm_eq_pos_add_pos(s_lhs_v.second, rhs, s_rhs);
        return mk_app({mk_const(*g_neg_add_pos2), type, mk_add_comm_group(type), s_lhs_v.second, s_rhs, rhs, sum_pr});
    }
}


expr norm_num_context::mk_norm_eq_pos_add_neg(expr & s_lhs, expr & s_rhs, expr & rhs) {
    expr prf = mk_norm_eq_neg_add_pos(s_rhs, s_lhs, rhs);
    expr type = get_type_and_arg_of_neg(s_rhs).first;
    return mk_app({mk_const(*g_pos_add_neg), type, mk_add_comm_group(type), s_lhs, s_rhs, rhs, prf});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_add_pos(expr & s_lhs, expr & s_rhs, expr & rhs) {
    lean_assert(!is_neg(s_lhs));
    lean_assert(!is_neg(s_rhs));
    lean_assert(!is_neg(rhs));
    auto p = mk_norm_add(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}


/*expr norm_num_context::mk_norm_eq(expr const & lhs, expr const & rhs) { // rhs is a nonneg numeral
    buffer<expr> args;
    expr f = get_app_args(lhs, args);
    if (!is_constant(f)) {
        throw exception("cannot take norm of nonconstant");
    }
//    m_lvls = const_levels(f);
//    expr rv;
//    expr prf;
    if (const_name(f) == *g_add && args.size() == 4) {
        auto lhs_p = num_of_expr(args[2]); // mk_norm_expr(args[2]);
        auto rhs_p = num_of_expr(args[3]); //mk_norm_expr(args[3]);
        buffer<expr> args_lhs, args_rhs;
//        expr flhs = get_app_args(lhs_p.first, args_lhs);
//        expr frhs = get_app_args(rhs_p.first, args_rhs);
//        std::cout << "in mk_norm_eq add. is_neg first, second:" << is_neg(lhs_p.first) << is_neg(rhs_p.first) << "\n";
        if (lhs_p.is_neg()) {
            if (rhs_p.is_neg()) {
                return mk_norm_eq_neg_add_neg(f, rhs, args);
                //return mk_norm_eq_neg_add_neg(f, rhs, args, args_lhs, args_rhs, lhs_p.second, rhs_p.second);
            } else {
                return mk_norm_eq_neg_add_pos(f, rhs, args);
            }
        } else {
            if (rhs_p.is_neg()) {
                buffer<expr> rvargs = buffer<expr>(args);
                rvargs[3] = args[2];
                rvargs[2] = args[3];
                expr commprf = mk_norm_eq_neg_add_pos(f, rhs, rvargs);
                // commprf : args[3] + args[2] = rhs
                return mk_app({mk_const(*g_pos_add_neg), args[0], mk_add_comm_group(args[0]), args[2], args[3], rhs, commprf});
            } else { // nonneg add nonneg
                return mk_norm_eq_pos_add_pos(f, rhs, args);
            }
        }
        } else if (const_name(f) == *g_mul && args.size() == 4) {
        auto lhs_p = mk_norm_expr(args[2]);
        auto rhs_p = mk_norm_expr(args[3]);// TODO(Rob): handle case where either is neg
        auto mul_p = mk_norm_mul(lhs_p.first, rhs_p.first);
        rv = mul_p.first;
        prf = mk_app({mk_const(*g_subst_prod), args[0], mk_has_mul(args[0]), args[2], args[3],
                          lhs_p.first, rhs_p.first, mul_p.first, lhs_p.second, rhs_p.second, mul_p.second});
    } else if (const_name(f) == *g_sub && args.size() == 4) {
        // auto lhs_p = mk_norm_expr(args[2]);
        // auto rhs_p = mk_norm_expr(args[3]);
        expr addneg = mk_app({mk_const(*g_add), args[0], mk_has_add(args[0]), args[2], mk_neg(args[0], args[3])});
        expr prf = mk_norm_eq(addneg, rhs); // a + -b = c
        return mk_app({mk_const(*g_sub_eq_add_neg), args[0], mk_add_comm_group(args[0]), args[2], args[3], rhs, prf});
    } else if ((const_name(f) == get_bit0_name() || const_name(f) == *g_neg)  && args.size() == 3) {
        auto arg = mk_norm(args[2]);
        // rv = mk_app({f, args[0], args[1], arg.first});
        return mk_cong(mk_app({f, args[0], args[1]}), args[0], args[2], arg.first, arg.second);
    } else if (const_name(f) == get_bit1_name() && args.size() == 4) {
        auto arg = mk_norm(args[3]);
        // rv = mk_app({f, args[0], args[1], args[2], arg.first});
        return mk_cong(mk_app({f, args[0], args[1], args[2]}), args[0], args[3], arg.first, arg.second);
    } else if ((const_name(f) == get_zero_name() || const_name(f) == get_one_name()) && args.size() == 2) {
        //rv = lhs;
        return mk_app({mk_const(*g_mk_eq), args[0], lhs});
    } else {
        std::cout << "error with name " << const_name(f) << " and size " << args.size() << ".\n";
        throw exception("mk_norm found unrecognized combo ");
    }
    // throw exception("not implemented yet");
}*/

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

expr norm_num_context::mk_neg(expr const & type, expr const & e) {
    auto has_neg = mk_has_neg(type);
    return mk_app({mk_const(*g_neg), type, has_neg, e});
}

expr norm_num_context::mk_add(expr const & type, expr const & e1, expr const & e2) {
    auto has_add = mk_has_add(type);
    return mk_app({mk_const(*g_add), type, has_add, e1, e2});
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    std::cout << "mk_norm\n";
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f) || args.size() == 0) {
        throw exception("malformed argument to mk_norm_expr");
    }
    m_lvls = const_levels(f);
    expr type = args[0];
    auto val = num_of_expr(e);
    expr nval; // e = nval
    if (val >= 0) {
        nval = from_num(val, type);
    } else {
        nval = mk_neg(type, from_num(neg(val), type));
    }
    if (const_name(f) == *g_add && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        expr prf;
        if (is_neg(lhs_p.first)) {
            if (is_neg(rhs_p.first)) {
                prf = mk_norm_eq_neg_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_neg_add_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg(rhs_p.first)) {
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
        lean_assert(num_of_expr(prf.first) == neg(val));
        if (is_neg(nval)) {
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            auto rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2], nval_args[2], prf.second);
            return pair<expr, expr>(nval, rprf);
        } else {
            auto rprf = mk_app({mk_const(*g_neg_neg), type, mk_add_group(type), args[2], nval, prf.second});
            return pair<expr, expr>(nval, rprf);
        }
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
        return pair<expr, expr>(e, mk_app({mk_const(*g_mk_eq), args[0], e}));
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
    g_monoid        = new name("algebra", "monoid");
    g_add_comm      = new name("algebra", "add_comm_semigroup");
    g_add_group      = new name("algebra", "add_group");
    g_mul_zero_class      = new name("algebra", "mul_zero_class");
    g_distrib       = new name("algebra", "distrib");
    g_has_neg       = new name("has_neg"); //"algebra",
    g_has_sub       = new name("algebra", "has_sub");
    g_semiring      = new name("algebra", "semiring");
    g_eq_neg_of_add_eq_zero = new name("algebra", "eq_neg_of_add_eq_zero");
    g_neg_add_neg_eq = new name("neg_add_neg_helper");
    g_neg_add_pos1 = new name("neg_add_pos_helper1");
    g_neg_add_pos2 = new name("neg_add_pos_helper2");
    g_pos_add_neg = new name("pos_add_neg_helper");
    g_sub_eq_add_neg = new name("sub_eq_add_neg_helper");
    g_pos_add_pos = new name("pos_add_pos_helper");
    g_neg_neg = new name("neg_neg_helper");
    g_add_comm_group = new name("algebra", "add_comm_group");
}

void finalize_norm_num() {
    delete g_add;
    delete g_add1;
    delete g_mul;
    delete g_sub;
    delete g_neg;
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
    delete g_add_comm;
    delete g_add_group;
    delete g_mul_zero_class;
    delete g_distrib;
    delete g_has_neg;
    delete g_has_sub;
    delete g_semiring;
    delete g_eq_neg_of_add_eq_zero;
    delete g_neg_add_neg_eq;
    delete g_neg_add_pos1;
    delete g_neg_add_pos2;
    delete g_pos_add_neg;
    delete g_pos_add_pos;
    delete g_sub_eq_add_neg;
    delete g_neg_neg;
    delete g_add_comm_group;
}
}
