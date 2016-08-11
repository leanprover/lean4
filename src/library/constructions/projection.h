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

void initialize_def_projection();
void finalize_def_projection();
}
