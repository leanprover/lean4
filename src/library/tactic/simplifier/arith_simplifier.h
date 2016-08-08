/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/arith_instance_manager.h"
#include "library/tactic/simplifier/simplifier.h"

namespace lean {

struct arith_simplifier_options {
    bool m_distribute_mul;
    arith_simplifier_options(options const & opts);
};

class arith_simplifier {
private:
    // Note: we use a [type_context *] instead of a [type_context &]
    // because some consumers may not have a [type_context] and may only want to
    // simplify concrete arith types.
    type_context                 * m_tctx_ptr;
    arith_simplifier_options       m_options;
    arith_instance_info_ref        m_arith_info;

    optional<expr>   simplify_eq(expr const & prefix, buffer<expr> const & args);

    optional<expr>   simplify_lt(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_gt(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_le(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_ge(expr const & prefix, buffer<expr> const & args);

    optional<expr>   simplify_add(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_mul(expr const & prefix, buffer<expr> const & args);

    optional<expr>   simplify_neg(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_sub(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_inv(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_div(expr const & prefix, buffer<expr> const & args);

    optional<expr>   simplify_numeral(expr const & prefix, buffer<expr> const & args);

    optional<expr>   simplify_int_of_nat(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_rat_of_int(expr const & prefix, buffer<expr> const & args);
    optional<expr>   simplify_real_of_rat(expr const & prefix, buffer<expr> const & args);

public:
    simp_result simplify_binary(expr const & e);
    optional<simp_result> simplify_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> & args);

    arith_simplifier(type_context & tctx): m_tctx_ptr(&tctx), m_options(tctx.get_options()) {}
};

void initialize_arith_simplifier();
void finalize_arith_simplifier();
}
