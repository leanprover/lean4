/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/

#include "library/norm_num.h"
#include "library/constants.cpp"
namespace lean {
  static name * g_add           = nullptr,
              * g_add1          = nullptr,
              * g_mul           = nullptr,
              * g_sub           = nullptr,
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
              * g_mul_zero_class= nullptr,
              * g_distrib       = nullptr,
              * g_semiring      = nullptr;
 

static bool is_numeral_aux(expr const & e, bool is_first) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (!is_constant(f)) {
      return false;
    }
    if (const_name(f) == *g_one) {
        return args.size() == 2;
    } else if (const_name(f) == *g_zero) {
        return is_first && args.size() == 2;
    } else if (const_name(f) == *g_bit1 || const_name(f) == *g_bit0) {
        return args.size() == 3 && is_numeral_aux(args[2], false);
    }
    return false;
}

bool norm_num_context::is_numeral(expr const & e) const {
    return is_numeral_aux(e, true);
}

/*
Takes e : instance A, and tries to synthesize has_add A.
*/
expr norm_num_context::mk_has_add(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_has_add, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_add instance");
    }
}

expr norm_num_context::mk_has_mul(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_has_mul, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_mul instance");
    }
}

expr norm_num_context::mk_has_one(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_has_one, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_one instance");
    }
}

expr norm_num_context::mk_add_monoid(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_add_monoid, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_monoid instance");
    }
}

expr norm_num_context::mk_monoid(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_monoid, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize monoid instance");
    }
}

expr norm_num_context::mk_add_comm(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_add_comm, const_levels(f)), args[0]); 
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize add_comm_semigroup instance");
    }
}

expr norm_num_context::mk_has_distrib(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_distrib, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize has_distrib instance");
    }
}

expr norm_num_context::mk_mul_zero_class(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_mul_zero_class, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize mul_zero instance");
    }
}

expr norm_num_context::mk_semiring(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr t = mk_app(mk_constant(*g_semiring, const_levels(f)), args[0]);
    optional<expr> inst = mk_class_instance(m_env, m_ctx, t);
    if (inst) {
        return *inst;
    } else {
        throw exception("failed to synthesize semiring instance");
    }
}

expr norm_num_context::mk_const(name const & n) {
    return mk_constant(n, m_lvls);
}

expr norm_num_context::mk_cong(expr const & op, expr const & type, expr const & a, expr const & b, expr const & eq) {
    return mk_app({mk_const(*g_mk_cong), type, op, a, b, eq});
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
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
	expr prf = mk_app({mk_const(*g_subst_sum), args[0], mk_has_add(args[1]), args[2], args[3], 
	                  lhs_p.first, rhs_p.first, add_p.first, lhs_p.second, rhs_p.second, add_p.second});
	return pair<expr, expr>(add_p.first, prf);
    } else if (const_name(f) == *g_mul && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
	auto rhs_p = mk_norm(args[3]);
        auto mul_p = mk_norm_mul(lhs_p.first, rhs_p.first);
	expr prf = mk_app({mk_const(*g_subst_prod), args[0], mk_has_mul(args[1]), args[2], args[3], 
	                  lhs_p.first, rhs_p.first, mul_p.first, lhs_p.second, rhs_p.second, mul_p.second});
	return pair<expr, expr>(mul_p.first, prf);
    } else if (const_name(f) == *g_bit0  && args.size() == 3) {
        auto arg = mk_norm(args[2]);
	expr rv = mk_app({f, args[0], args[1], arg.first});
	expr prf = mk_cong(mk_app({f, args[0], args[1]}), args[0], args[2], arg.first, arg.second);
	return pair<expr, expr>(rv, prf);
    } else if (const_name(f) == *g_bit1 && args.size() == 4) {
        auto arg = mk_norm(args[3]);
	expr rv = mk_app({f, args[0], args[1], args[2], arg.first});
	expr prf = mk_cong(mk_app({f, args[0], args[1], args[2]}), args[0], args[3], arg.first, arg.second);
	return pair<expr, expr>(rv, prf);
    } else if ((const_name(f) == *g_zero || const_name(f) == *g_one) && args.size() == 2) {
        return pair<expr, expr>(e, mk_app({mk_const(*g_mk_eq), args[0], e}));
    } else {
        std::cout << "error with name " << const_name(f) << " and size " << args.size() << ".\n";
        throw exception("mk_norm found unrecognized combo ");
    }
    // TODO(Rob): cases for sub, div
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
    expr rv;
    expr prf;
    if (is_bit0(lhs) && is_bit0(rhs)) { // typec is has_add
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
	rv = mk_app(lhs_head, type, typec, p.first);
	prf = mk_app({mk_const(*g_bit0_add_bit0), type, mk_add_comm(typec), args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit0(lhs) && is_bit1(rhs)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[3]);
	rv = mk_app({rhs_head, type, args_rhs[1], args_rhs[2], p.first});
	prf = mk_app({mk_const(*g_bit0_add_bit1), type, mk_add_comm(typec), args_rhs[1], args_lhs[2], args_rhs[3], p.first, p.second});
    } else if (is_bit0(lhs) && is_one(rhs)) {
        rv = mk_app({mk_const(*g_bit1), type, args_rhs[1], args_lhs[1], args_lhs[2]});
        prf = mk_app({mk_const(*g_bit0_add_1), type, typec, args_rhs[1], args_lhs[2]});
    } else if (is_bit1(lhs) && is_bit0(rhs)) { // typec is has_one
        auto p = mk_norm_add(args_lhs[3], args_rhs[2]);
	rv = mk_app(lhs_head, type, typec, args_lhs[2], p.first);
	prf = mk_app({mk_const(*g_bit1_add_bit0), type, mk_add_comm(typec), typec, args_lhs[3], args_rhs[2], p.first, p.second});
    } else if (is_bit1(lhs) && is_bit1(rhs)) { // typec is has_one
	auto add_ts = mk_norm_add(args_lhs[3], args_rhs[3]);
        expr add1 = mk_app({mk_const(*g_add1), type, args_lhs[2], typec, add_ts.first});
	auto p = mk_norm_add1(add1);
        rv = mk_app({mk_const(*g_bit0), type, args_lhs[2], p.first});
	prf = mk_app({mk_const(*g_bit1_add_bit1), type, mk_add_comm(typec), typec, args_lhs[3], args_rhs[3], add_ts.first, p.first, add_ts.second, p.second});
    } else if (is_bit1(lhs) && is_one(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(*g_add1), type, args_lhs[2], typec, lhs});
	auto p = mk_norm_add1(add1);
	rv = p.first;
	prf = mk_app({mk_const(*g_bit1_add_1), type, args_lhs[2], typec, args_lhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_bit0(rhs)) { // typec is has_one
        rv = mk_app({mk_const(*g_bit1), type, typec, args_rhs[1], args_rhs[2]});
        prf = mk_app({mk_const(*g_1_add_bit0), type, mk_add_comm(typec), typec, args_rhs[2]});
    } else if (is_one(lhs) && is_bit1(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(*g_add1), type, args_rhs[2], args_rhs[1], rhs});
	auto p = mk_norm_add1(add1);
	rv = p.first;
	prf = mk_app({mk_const(*g_1_add_bit1), type, mk_add_comm(typec), typec, args_rhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_one(rhs)) {
      rv = mk_app({mk_const(*g_bit0), type, mk_has_add(typec), lhs});
	prf = mk_app({mk_const(*g_one_add_one), type, mk_has_add(typec), typec});
    } else if (is_zero(lhs)) {
        rv = rhs;
        prf = mk_app({mk_const(*g_bin_0_add), type, mk_add_monoid(typec), rhs});
    } else if (is_zero(rhs)) {
        rv = lhs;
        prf = mk_app({mk_const(*g_bin_add_0), type, mk_add_monoid(typec), lhs});
    }
    else {
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
        rv = mk_app({mk_const(*g_bit1), args[0], args[2], args[1], ne_args[2]});
	prf = mk_app({mk_const(*g_add1_bit0), args[0], args[1], args[2], ne_args[2]});
    } else if (is_bit1(p)) { // ne_args : has_one, has_add
        auto np = mk_norm_add1(mk_app({mk_const(*g_add1), args[0], args[1], args[2], ne_args[3]}));
	rv = mk_app({mk_const(*g_bit0), args[0], args[1], np.first});
	prf = mk_app({mk_const(*g_add1_bit1), args[0], mk_add_comm(args[1]), args[2], ne_args[3], np.first, np.second});
    } else if (is_zero(p)) {
        rv = mk_app({mk_const(*g_one), args[0], args[2]});
	prf = mk_app({mk_const(*g_add1_zero), args[0], mk_add_monoid(args[1]), args[2]});
    } else if (is_one(p)) {
        rv = mk_app({mk_const(*g_bit0), args[0], args[1], mk_app({mk_const(*g_one), args[0], args[2]})});
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
        prf = mk_app({mk_const(*g_mul_zero), type, mk_mul_zero_class(typec), lhs});
    } else if (is_zero(lhs)) {
        rv = lhs;
	prf = mk_app({mk_const(*g_zero_mul), type, mk_mul_zero_class(typec), rhs});
    } else if (is_one(rhs)) {
        rv = lhs;
        prf = mk_app({mk_const(*g_mul_one), type, mk_monoid(typec), lhs});
    } else if (is_bit0(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[2]);
        rv = mk_app({rhs_head, type, typec, mtp.first});
        prf = mk_app({mk_const(*g_mul_bit0), type, mk_has_distrib(typec), lhs, args_rhs[2], mtp.first, mtp.second});
    } else if (is_bit1(rhs)) {
      std::cout << "is_bit1 " << rhs << "\n";
        auto mtp = mk_norm_mul(lhs, args_rhs[3]);
        auto atp = mk_norm_add(mk_app({mk_const(*g_bit0), type, args_rhs[2], mtp.first}), lhs);
	rv = atp.first;
	prf = mk_app({mk_const(*g_mul_bit1), type, mk_semiring(typec), lhs, args_rhs[3],
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

void initialize_norm_num() {
  g_add     = new name("add"); 
  g_add1    = new name("add1");
  g_mul     = new name("mul");
  g_sub     = new name("sub");
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
  g_mul_zero_class      = new name("algebra", "mul_zero_class");
  g_distrib       = new name("algebra", "distrib");
  g_semiring      = new name("algebra", "semiring");
}

void finalize_norm_num() {
  delete g_add;
  delete g_add1;
  delete g_mul;
  delete g_sub;
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
  delete g_mul_zero_class;
  delete g_distrib;
  delete g_semiring;
}
}
