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
name_set collect_univ_params(expr const & e, name_set const & ls = name_set());
void collect_locals(expr const & e, expr_struct_set & ls);
level_param_names to_level_param_names(name_set const & ls);

/** \brief Return true iff \c [begin_locals, end_locals) contains \c local */
template<typename It> bool contains_local(expr const & local, It const & begin_locals, It const & end_locals) {
    return std::any_of(begin_locals, end_locals, [&](expr const & l) { return mlocal_name(local) == mlocal_name(l); });
}

/** \brief Return true iff \c locals contains \c local */
inline bool contains_local(expr const & local, buffer<expr> const & locals) {
    return contains_local(local, locals.begin(), locals.end());
}
}
