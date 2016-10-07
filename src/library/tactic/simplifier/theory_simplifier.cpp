/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/name_hash_map.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/num.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/simplifier/util.h"
#include "library/tactic/simplifier/theory_simplifier.h"

#ifndef LEAN_DEFAULT_THEORY_SIMPLIFIER_DISTRIBUTE_MUL
#define LEAN_DEFAULT_THEORY_SIMPLIFIER_DISTRIBUTE_MUL true
#endif

namespace lean {

// Theory simplifier
theory_simplifier::theory_simplifier(type_context & tctx): m_tctx(tctx), m_prop_simplifier(tctx) {}

bool theory_simplifier::owns(expr const & e) {
    return static_cast<bool>(to_num(e));
}

simp_result theory_simplifier::simplify_binary(expr const & e) {
    simp_result r_prop = m_prop_simplifier.simplify_binary(e);
    if (r_prop.get_new() != e)
        return r_prop;

    return simp_result(e);
}

optional<simp_result> theory_simplifier::simplify_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> & args) {
    if (auto r_prop = m_prop_simplifier.simplify_nary(assoc, old_e, op, args))
        return r_prop;

    return optional<simp_result>();
}

void initialize_theory_simplifier() {
}

void finalize_theory_simplifier() {
}
}
