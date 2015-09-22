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
// The hash-consing tables are thread local.

// Remark: All procedures assume the children levels and expressions are maximally shared.
// That is, it assumes they have been created using the APIs provided by this module.

// Auxiliary object for resetting the the thread local hash-consing tables.
// Its destructor restores the state of the hash-consing tables.
class scope_hash_consing {
    void * m_level_table;
    void * m_expr_table;
    void * m_var_array;
    void * m_mref_array;
    void * m_lref_array;
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
level mk_meta_univ(name const & n);

expr mk_var(unsigned idx);
// Remark: lref and mref expressions are implemented using kernel macros.
// We use them to encode local constants and meta-variables in the blast tactic.
expr mk_lref(unsigned idx);
expr mk_mref(unsigned idx);
expr mk_sort(level const & l);
expr mk_constant(name const & n, levels const & ls);
expr mk_app(expr const & f, expr const & a);
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

// Return true iff \c e is a lref of mref.
bool is_lmref(expr const & e);
bool is_mref(expr const & e);
bool is_lref(expr const & e);
/** \brief Return the index of the give lref/mref.
    \pre is_mref(e) || is_lref(e) */
unsigned get_lmindex(expr const & e);

level update_succ(level const & l, level const & new_arg);
level update_max(level const & l, level const & new_lhs, level const & new_rhs);

level replace(level const & l, std::function<optional<level>(level const & l)> const & f);

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg);
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body);
expr update_sort(expr const & e, level const & new_level);
expr update_constant(expr const & e, levels const & new_levels);
expr update_macro(expr const & e, unsigned num, expr const * args);

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f) {
    return blast::replace(e, [&](expr const & e, unsigned) { return f(e); });
}

expr lift_free_vars(expr const & e, unsigned s, unsigned d);
expr lift_free_vars(expr const & e, unsigned d);

expr instantiate(expr const & e, unsigned n, expr const * s);
expr instantiate_rev(expr const & e, unsigned n, expr const * s);

level instantiate(level const & l, level_param_names const & ps, levels const & ls);
expr  instantiate_univ_params(expr const & e, level_param_names const & ps, levels const & ls);
expr  instantiate_type_univ_params(declaration const & d, levels const & ls);
expr  instantiate_value_univ_params(declaration const & d, levels const & ls);

expr abstract_lrefs(expr const & e, unsigned n, expr const * s);
}
}
