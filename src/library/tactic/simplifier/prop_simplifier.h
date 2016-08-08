/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/arith_instance_manager.h"
#include "library/tactic/simplifier/simplifier.h"

namespace lean {

struct prop_simplifier_options {
    bool m_elim_and;
    prop_simplifier_options(options const & opts);
};

class prop_simplifier {
private:
    type_context                 & m_tctx;
    prop_simplifier_options        m_options;

    optional<expr> simplify_eq(expr const & eq, expr const & type, expr const & lhs, expr const & rhs);
    optional<expr> simplify_heq(expr const & heq, expr const & type1, expr const & type2, expr const & lhs, expr const & rhs);
    optional<expr> simplify_iff(expr const & lhs, expr const & rhs);
    optional<expr> simplify_ite(expr const & fn, buffer<expr> & args);

    optional<expr> simplify_not(expr const & e);
    optional<expr> simplify_pi(expr const & dom, expr const & body, bool is_arrow);

    optional<expr> simplify_and(buffer<expr> & args);
    optional<expr> simplify_or(buffer<expr> & args);

public:
    simp_result simplify_binary(expr const & e);
    optional<simp_result> simplify_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> & args);

    prop_simplifier(type_context & tctx): m_tctx(tctx), m_options(tctx.get_options()) {}
};

void initialize_prop_simplifier();
void finalize_prop_simplifier();
}
