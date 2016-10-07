/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/arith_instance_manager.h"
#include "library/tactic/simplifier/simplifier.h"
#include "library/tactic/simplifier/prop_simplifier.h"

namespace lean {

class theory_simplifier {
private:
    // Note: may need to be a [type_context *] for simplex
    type_context                 & m_tctx;

    prop_simplifier                m_prop_simplifier;

    optional<simp_result> simplify_eq(expr const & prefix, buffer<expr> const & args);

public:
    enum class dispatch_id {
        EQ,
        // Prop
            AND, OR, NOT, XOR, IMPLIES, ITE,
            };

    enum class dispatch_kind { DEFAULT, NARY_ASSOC, OWNS_SUBTERMS };
    typedef std::tuple<dispatch_id, dispatch_kind, unsigned> dispatch_info;

    theory_simplifier(type_context & tctx);

    bool        owns(expr const & e);
    simp_result simplify_binary(expr const & e);
    optional<simp_result> simplify_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> & nary_args);
};

void initialize_theory_simplifier();
void finalize_theory_simplifier();
}
