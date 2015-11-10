/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#pragma once
#include "kernel/environment.h"
#include "library/local_context.h"
#include "library/num.h"
#include "library/class_instance_resolution.h"
#include "util/numerics/mpq.h"
#include <unordered_map>
#include <string>

namespace lean {

struct hash_name {
    size_t operator() (const name &n) const {
        return std::hash<std::string>()(n.to_string());
    }
};

class norm_num_context {
    environment   m_env;
    local_context m_ctx;
    levels        m_lvls;
    pair<expr, expr> mk_norm_add(expr const &, expr const &);
    pair<expr, expr> mk_norm_add1(expr const &);
    pair<expr, expr> mk_norm_mul(expr const &, expr const &);
    expr mk_const(name const & n);
    expr mk_cong(expr const &, expr const &, expr const &, expr const &, expr const &);
    expr mk_has_add(expr const &);
    expr mk_has_mul(expr const &);
    expr mk_has_zero(expr const &);
    expr mk_has_one(expr const &);
    expr mk_add_monoid(expr const &);
    expr mk_monoid(expr const &);
    expr mk_has_distrib(expr const &);
    expr mk_add_comm(expr const &);
    expr mk_add_group(expr const &);
    expr mk_mul_zero_class(expr const &);
    expr mk_ring(expr const &);
    expr mk_semiring(expr const &);
    expr mk_field(expr const &);
    expr mk_lin_ord_semiring(expr const &);
    expr mk_lin_ord_ring(expr const &);
    expr mk_wk_order(expr const &);
    expr mk_has_neg(expr const &);
    expr mk_has_div(expr const &);
    expr mk_has_sub(expr const &);
    expr mk_add(expr const &, expr const &, expr const &);
    expr mk_mul(expr const &, expr const &, expr const &);
    expr mk_div(expr const &, expr const &, expr const &);
    expr mk_neg(expr const &, expr const &);
    expr mk_add_comm_group(expr const &);
    expr mk_pos_prf(expr const &);
    expr mk_nonneg_prf(expr const &);
    expr mk_norm_eq_neg_add_neg(expr &, expr &, expr &);
    expr mk_norm_eq_neg_add_pos(expr &, expr &, expr &);
    expr mk_norm_eq_pos_add_neg(expr &, expr &, expr &);
    expr mk_norm_eq_pos_add_pos(expr &, expr &, expr &);
    expr mk_norm_eq_neg_mul_neg(expr &, expr &, expr &);
    expr mk_norm_eq_neg_mul_pos(expr &, expr &, expr &);
    expr mk_norm_eq_pos_mul_neg(expr &, expr &, expr &);
    expr mk_norm_eq_pos_mul_pos(expr &, expr &, expr &);
    expr mk_norm_div_add(expr &, expr &, expr &);
    expr mk_norm_add_div(expr &, expr &, expr &);
    expr mk_norm_div_mul(expr &, expr &, expr &);
    expr mk_norm_mul_div(expr &, expr &, expr &);
    expr mk_nonzero_prf(expr const & e);
    pair<expr, expr> get_type_and_arg_of_neg(expr &);
    std::unordered_map<name, expr, hash_name> instances;

public:
    norm_num_context(environment const & env, local_context const & ctx):m_env(env), m_ctx(ctx) {}

    bool is_numeral(expr const & e) const;
    bool is_neg_app(expr const &) const;
    bool is_div(expr const &) const;
    pair<expr, expr> mk_norm(expr const & e);
    expr mk_norm_eq(expr const &, expr const &);
    mpz num_of_expr(expr const & e);
    mpq mpq_of_expr(expr const & e);
    optional<mpq> to_mpq(expr const & e);
    expr from_pos_num(mpz const &, expr const &);
    expr from_num(mpz const &, expr const &);
    expr from_mpq(mpq const &, expr const &);
};

inline bool is_neg(expr const & e);

inline bool is_numeral(environment const & env, expr const & e) {
    return norm_num_context(env, local_context()).is_numeral(e);
}

inline pair<expr, expr> mk_norm_num(environment const & env, local_context const & ctx, expr const & e) {
    return norm_num_context(env, ctx).mk_norm(e);
}

inline mpz num_of_expr(environment const & env, local_context const & ctx, expr const & e) {
    return norm_num_context(env, ctx).num_of_expr(e);
}

inline mpq mpq_of_expr(environment const & env, local_context const & ctx, expr const & e) {
    return norm_num_context(env, ctx).mpq_of_expr(e);
}

void initialize_norm_num();
void finalize_norm_num();
}
