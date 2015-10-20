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

namespace lean {
class norm_num_context {
    environment   m_env;
    local_context m_ctx;
    levels        m_lvls;
    pair<expr, expr> mk_norm_add(expr const &, expr const &);
    pair<expr, expr> mk_norm_add1(expr const &);
    pair<expr, expr> mk_norm_mul(expr const &, expr const &);
    pair<expr, expr> mk_norm_div(expr const &, expr const &);
    pair<expr, expr> mk_norm_sub(expr const &, expr const &);
    expr mk_const(name const & n);
    expr mk_cong(expr const &, expr const &, expr const &, expr const &, expr const &);
    expr mk_has_add(expr const &);
    expr mk_has_mul(expr const &);
    expr mk_has_one(expr const &);
    expr mk_add_monoid(expr const &);
    expr mk_monoid(expr const &);
    expr mk_has_distrib(expr const &);
    expr mk_add_comm(expr const &);
    expr mk_mul_zero_class(expr const &);
    expr mk_semiring(expr const &);

public:
    norm_num_context(environment const & env, local_context const & ctx):m_env(env), m_ctx(ctx) {}

    bool is_numeral(expr const & e) const;
    pair<expr, expr> mk_norm(expr const & e);
};

inline bool is_numeral(environment const & env, expr const & e) {
    return norm_num_context(env, local_context()).is_numeral(e);
}

inline pair<expr, expr> mk_norm_num(environment const & env, local_context const & ctx, expr const & e) {
    return norm_num_context(env, ctx).mk_norm(e);
}
void initialize_norm_num();
void finalize_norm_num();
}
