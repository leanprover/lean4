/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/sexpr/option_declarations.h"
#include "library/constants.h"
#include "library/tactic/simplifier/arith_simplifier.h"

#ifndef LEAN_DEFAULT_ARITH_SIMPLIFIER_DISTRIBUTE_MUL
#define LEAN_DEFAULT_ARITH_SIMPLIFIER_DISTRIBUTE_MUL true
#endif

namespace lean {

// Options
static name * g_arith_simplifier_distribute_mul = nullptr;

static bool get_arith_simplifier_distribute_mul(options const & o) {
    return o.get_bool(*g_arith_simplifier_distribute_mul, LEAN_DEFAULT_ARITH_SIMPLIFIER_DISTRIBUTE_MUL);
}

arith_simplifier_options::arith_simplifier_options(options const & o):
    m_distribute_mul(get_arith_simplifier_distribute_mul(o)) {}

// Setup and teardown
void initialize_arith_simplifier() {
    // Option names
    g_arith_simplifier_distribute_mul     = new name{"arith_simplifier", "distribute_mul"};

    // Register options
    register_bool_option(*g_arith_simplifier_distribute_mul, LEAN_DEFAULT_ARITH_SIMPLIFIER_DISTRIBUTE_MUL,
                         "(arith_simplifier) distribute mul over add");
}

void finalize_arith_simplifier() {
    // Option names
    delete g_arith_simplifier_distribute_mul;
}

// Entry points
simp_result arith_simplifier::simplify_binary(expr const & old_e) {
    return simp_result(old_e);
}

optional<simp_result> arith_simplifier::simplify_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> & args) {
    return optional<simp_result>();
}

}
