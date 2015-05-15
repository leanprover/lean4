/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_set.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
namespace lean {
void collect_univ_params_core(level const & l, name_set & r);
name_set collect_univ_params(expr const & e, name_set const & ls = name_set());
/**
  \remark If restricted is true, then locals in meta-variable applications and local constants
  are ignored.
*/
void collect_locals(expr const & e, expr_struct_set & ls, bool restricted = false);
level_param_names to_level_param_names(name_set const & ls);

/** \brief Return true iff \c [begin_locals, end_locals) contains \c local */
template<typename It>
bool contains_local(expr const & local, It const & begin_locals, It const & end_locals) {
    return std::any_of(begin_locals, end_locals, [&](expr const & l) { return mlocal_name(local) == mlocal_name(l); });
}

template<typename T>
bool contains_local(expr const & l, T const & locals) {
    return std::any_of(locals.begin(), locals.end(),
                       [&](expr const & l1) { return mlocal_name(l1) == mlocal_name(l); });
}

/** \brief Return true iff \c e contains a local constant named \c n (it uses mlocal_name) */
bool contains_local(expr const & e, name const & n);

/** \brief Return true iff \e contains the local constant \c h */
inline bool depends_on(expr const & e, expr const & h) {
    return contains_local(e, mlocal_name(h));
}

/** \brief Return true iff one of \c es contains the local constant \c h */
optional<expr> depends_on(unsigned sz, expr const * es, expr const & h);

/** \brief Return true iff \c e depends on any of the local constants in \c hs */
bool depends_on_any(expr const & e, unsigned hs_sz, expr const * hs);
inline bool depends_on_any(expr const & e, buffer<expr> const & hs) {
    return depends_on_any(e, hs.size(), hs.data());
}
}
