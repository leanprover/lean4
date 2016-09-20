/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Auxiliary information attached to projections. This information
    is used to simplify projection over constructor (efficiently).

    That is, given a projection pr_i associated with the constructor mk
    where A are parameters, we want to implement the following reduction
    efficiently. The idea is to avoid unfolding pr_i.

       pr_i A (mk A f_1 ... f_n) ==> f_i

    We also use this information in the rewriter/simplifier.
*/
struct projection_info {
    name     m_constructor;   // mk in the rule above
    unsigned m_nparams;       // number of parameters of the inductive datatype
    unsigned m_i;             // i in the rule above
    bool     m_inst_implicit; // true if it is the projection of a "class"

    projection_info() {}
    projection_info(name const & c, unsigned nparams, unsigned i, bool inst_implicit):
        m_constructor(c), m_nparams(nparams), m_i(i), m_inst_implicit(inst_implicit) {}
};

/** \brief Mark \c p as a projection in the given environment and store that
    \c mk is the constructor associated with it, \c nparams is the number of parameters, and
    \c i says that \c p is the i-th projection.
*/
environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i,
                                 bool inst_implicit);

/** \brief If \c p is a projection in the given environment, then return the information
    associated with it (constructor, number of parameters, and index).
    If \c p is not a projection, then return nullptr.
*/
projection_info const * get_projection_info(environment const & env, name const & p);

inline bool is_projection(environment const & env, name const & n) {
    return get_projection_info(env, n) != nullptr;
}

/** \brief Return the mapping from projection name to associated information */
name_map<projection_info> const & get_projection_info_map(environment const & env);

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure_like(environment const & env, name const & S);

void initialize_projection();
void finalize_projection();
}
