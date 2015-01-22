/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Create projections operators for the structure named \c n.
    The procedure assumes \c n is a structure.

    The argument \c infer_k specifies the implicit argument inference strategy used for the
    structure parameters.

    If \c inst_implicit == true, then the structure argument of the projection is decorated as
    "instance implicit"
             [s : n]
*/
environment mk_projections(environment const & env, name const & n, buffer<name> const & proj_names,
                           implicit_infer_kind infer_k = implicit_infer_kind::Implicit, bool inst_implicit = false);
environment mk_projections(environment const & env, name const & n,
                           implicit_infer_kind infer_k = implicit_infer_kind::Implicit, bool inst_implicit = false);

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure(environment const & env, name const & S);

/** \brief Auxiliary information attached to projections. This information
    is used to simplify projection over constructor (efficiently)

    That is, given a projection pr_i associated with the constructor mk
    where A are parameters, we want to implement the following reduction
    efficiently. The idea is to avoid unfolding pr_i.

       pr_i A (mk A f_1 ... f_n) ==> f_i

*/
struct projection_info {
    name     m_constructor; // mk in the rule above
    unsigned m_nparams;     // number of parameters of the inductive datatype
    unsigned m_i;           // i in the rule above
    projection_info() {}
    projection_info(name const & c, unsigned nparams, unsigned i):
        m_constructor(c), m_nparams(nparams), m_i(i) {}
};

/** \brief If \c p is a projection in the given environment, then return the information
    associated with it (constructor, number of parameters, and index).
    If \c p is not a projection, then return nullptr.
*/
projection_info const * get_projection_info(environment const & env, name const & p);

/** \brief Create a projection macro term that can peform the following reduction efficiently

       pr_i A (mk A f_1 ... f_n) ==> f_i

    \remark proj_name is the name of the definition that implements the actual projection.
*/
expr mk_projection_macro(name const & proj_name, expr const & e);

void initialize_projection();
void finalize_projection();
}
