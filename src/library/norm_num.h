/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#pragma once
#include <unordered_map>
#include <string>
#include "util/name_map.h"
#include "util/numerics/mpq.h"
#include "kernel/environment.h"
#include "library/type_context.h"
#include "library/num.h"
#include "library/arith_instance.h"

namespace lean {
class norm_num_context {
    type_context_old & m_ctx;
    arith_instance m_ainst;

    pair<expr, expr> mk_norm_add(expr const &, expr const &);
    pair<expr, expr> mk_norm_add1(expr const &);
    pair<expr, expr> mk_norm_mul(expr const &, expr const &);
    expr mk_const(name const & n);
    expr mk_cong(expr const &, expr const &, expr const &, expr const &, expr const &);
    expr mk_zero() { return m_ainst.mk_zero(); }
    expr mk_one() { return m_ainst.mk_one(); }
    expr mk_add(expr const & e1, expr const & e2) { return mk_app(m_ainst.mk_add(), e1, e2); }
    expr mk_neg(expr const & e) { return mk_app(m_ainst.mk_neg(), e); }
    expr mk_mul(expr const & e1, expr const & e2) { return mk_app(m_ainst.mk_mul(), e1, e2); }
    expr mk_div(expr const & e1, expr const & e2) { return mk_app(m_ainst.mk_div(), e1, e2); }
    expr mk_bit0(expr const & e1) { return mk_app(m_ainst.mk_bit0(), e1); }
    expr mk_bit1(expr const & e1) { return mk_app(m_ainst.mk_bit1(), e1); }

    expr mk_has_zero() { return m_ainst.mk_has_zero(); }
    expr mk_has_one() { return m_ainst.mk_has_one(); }
    expr mk_has_add() { return m_ainst.mk_has_add(); }
    expr mk_has_sub() { return m_ainst.mk_has_sub(); }
    expr mk_has_neg() { return m_ainst.mk_has_neg(); }
    expr mk_has_mul() { return m_ainst.mk_has_mul(); }
    expr mk_has_div() { return m_ainst.mk_has_div(); }

    expr mk_add_monoid() { return m_ainst.mk_add_monoid(); }
    expr mk_monoid() { return m_ainst.mk_monoid(); }
    expr mk_distrib() { return m_ainst.mk_distrib(); }
    expr mk_add_comm() { return m_ainst.mk_add_comm_semigroup(); }
    expr mk_add_comm_group() { return m_ainst.mk_add_comm_group(); }
    expr mk_add_group() { return m_ainst.mk_add_group(); }
    expr mk_mul_zero_class() { return m_ainst.mk_mul_zero_class(); }
    expr mk_ring() { return m_ainst.mk_ring(); }
    expr mk_semiring() { return m_ainst.mk_semiring(); }
    expr mk_field() { return m_ainst.mk_field(); }
    expr mk_lin_ord_semiring() { return m_ainst.mk_linear_ordered_semiring(); }
    expr mk_lin_ord_ring() { return m_ainst.mk_linear_ordered_ring(); }
    expr mk_partial_order() { return m_ainst.mk_partial_order(); }

    expr mk_num(mpq const & q) { return m_ainst.mk_num(q); }

    expr mk_pos_prf(expr const &);
    expr mk_nonneg_prf(expr const &);
    expr mk_norm_eq_neg_add_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_neg_add_pos(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_add_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_add_pos(expr const &, expr const &, expr const &);
    expr mk_norm_eq_neg_mul_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_neg_mul_pos(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_mul_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_mul_pos(expr const &, expr const &, expr const &);
    expr mk_norm_div_add(expr const &, expr const &, expr const &);
    expr mk_norm_add_div(expr const &, expr const &, expr const &);
    expr mk_norm_div_mul(expr const &, expr const &, expr const &);
    expr mk_norm_mul_div(expr const &, expr const &, expr const &);
    expr_pair mk_norm_nat_sub(expr const &, expr const &);
    expr mk_nonzero_prf(expr const & e);
    pair<expr, expr> get_type_and_arg_of_neg(expr const &);

    bool is_numeral(expr const & e) const;
    bool is_neg_app(expr const &) const;
    bool is_div(expr const &) const;
    bool is_nat_const(expr const &) const;
    mpq mpq_of_expr(expr const & e);
    optional<mpq> to_mpq(expr const & e);
    expr mk_norm_eq(expr const &, expr const &);

public:
    norm_num_context(type_context_old & ctx): m_ctx(ctx), m_ainst(ctx) {}

    pair<expr, expr> mk_norm(expr const & e);
};

inline pair<expr, expr> mk_norm_num(type_context_old & ctx, expr const & e) {
    return norm_num_context(ctx).mk_norm(e);
}
}
