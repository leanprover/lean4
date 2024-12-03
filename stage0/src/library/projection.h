/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"

namespace lean {
/** \brief Auxiliary information attached to projections. This information
    is used to simplify projection over constructor (efficiently).

    That is, given a projection pr_i associated with the constructor mk
    where A are parameters, we want to implement the following reduction
    efficiently. The idea is to avoid unfolding pr_i.

       pr_i A (mk A f_1 ... f_n) ==> f_i

    We also use this information in the rewriter/simplifier.
*/
class projection_info : public object_ref {
public:
    projection_info(name const & c, unsigned nparams, unsigned i, bool inst_implicit);
    projection_info():projection_info(name(), 0, 0, false) {}
    projection_info(projection_info const & other):object_ref(other) {}
    projection_info(projection_info && other):object_ref(std::move(other)) {}
    /* low-level constructors */
    explicit projection_info(object * o):object_ref(o) {}
    explicit projection_info(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit projection_info(object_ref const & o):object_ref(o) {}
    projection_info & operator=(projection_info const & other) { object_ref::operator=(other); return *this; }
    projection_info & operator=(projection_info && other) { object_ref::operator=(std::move(other)); return *this; }
    name const & get_constructor() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 1)).get_small_value(); }
    unsigned get_i() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    bool is_inst_implicit() const;
};

/** \brief Mark \c p as a projection in the given elab_environment and store that
    \c mk is the constructor associated with it, \c nparams is the number of parameters, and
    \c i says that \c p is the i-th projection.
*/
elab_environment save_projection_info(elab_environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i,
                                 bool inst_implicit);

/** \brief If \c p is a projection in the given elab_environment, then return the information
    associated with it (constructor, number of parameters, and index).
    If \c p is not a projection, then return nullptr.
*/
optional<projection_info> get_projection_info(elab_environment const & env, name const & p);

inline bool is_projection(elab_environment const & env, name const & n) {
    return static_cast<bool>(get_projection_info(env, n));
}
}
