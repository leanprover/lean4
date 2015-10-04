/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/declaration.h"

namespace lean {
namespace blast {
// API for creating maximally shared terms used by the blast tactic.
// The API assumes there is a single blast tactic using theses terms.
// The expression hash-consing tables are thread local and implemented
// in the kernel

// Remark: All procedures assume the children levels and expressions are maximally shared.
// That is, it assumes they have been created using the APIs provided by this module.

// Auxiliary object for resetting the the thread local hash-consing tables.
// It also uses an assertion to make sure it is not being used in a recursion.
class scope_hash_consing : public scoped_expr_caching {
public:
    scope_hash_consing();
    ~scope_hash_consing();
};

level mk_level_zero();
level mk_level_one();
level mk_max(level const & l1, level const & l2);
level mk_imax(level const & l1, level const & l2);
level mk_succ(level const & l);
level mk_param_univ(name const & n);
level mk_global_univ(name const & n);
level mk_uref(unsigned idx);

bool is_uref(level const & l);
unsigned uref_index(level const & l);

expr mk_var(unsigned idx);
// mk_href and mk_mref are helper functions for creating hypotheses and meta-variables used in the blast tactic.
// Remark: the local constants and metavariables manipulated by the blast tactic do **not** store their types.
expr mk_href(unsigned idx);
expr mk_mref(unsigned idx);
expr mk_sort(level const & l);
expr mk_constant(name const & n, levels const & ls);
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi);
expr mk_app(expr const & f, expr const & a);
expr mk_app(expr const & f, unsigned num_args, expr const * args);
expr mk_app(unsigned num_args, expr const * args);
expr mk_rev_app(expr const & f, unsigned num_args, expr const * args);
expr mk_rev_app(unsigned num_args, expr const * args);
expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info const & bi);
inline expr mk_pi(name const & n, expr const & t, expr const & e, binder_info const & bi) {
    return blast::mk_binding(expr_kind::Pi, n, t, e, bi);
}
inline expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info const & bi) {
    return blast::mk_binding(expr_kind::Lambda, n, t, e, bi);
}
inline expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e) {
    return blast::mk_binding(k, n, t, e, binder_info());
}
inline expr mk_pi(name const & n, expr const & t, expr const & e) {
    return blast::mk_pi(n, t, e, binder_info());
}
inline expr mk_lambda(name const & n, expr const & t, expr const & e) {
    return blast::mk_lambda(n, t, e, binder_info());
}
expr mk_macro(macro_definition const & m, unsigned num, expr const * args);

bool is_href(expr const & e);
unsigned href_index(expr const & e);
bool is_mref(expr const & e);
unsigned mref_index(expr const & e);
/** \brief Return true iff \c e contain href's */
bool has_href(expr const & e);
/** \brief Return true iff \c e contain mref's */
bool has_mref(expr const & e);

bool is_local(expr const & e);
unsigned local_index(expr const & e);
expr const & local_type(expr const & e);
bool has_local(expr const & e);

level update_succ(level const & l, level const & new_arg);
level update_max(level const & l, level const & new_lhs, level const & new_rhs);

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg);
expr update_metavar(expr const & e, expr const & new_type);
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body);
expr update_sort(expr const & e, level const & new_level);
expr update_constant(expr const & e, levels const & new_levels);
expr update_local(expr const & e, expr const & new_type);
expr update_macro(expr const & e, unsigned num, expr const * args);

void initialize_expr();
void finalize_expr();
}
}
