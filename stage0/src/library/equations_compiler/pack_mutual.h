/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** \brief Create a new equations object containing a single function.
    The functions must be unary. */
expr pack_mutual(type_context_old & ctx, expr const & eqns);

expr mk_mutual_arg(type_context_old & ctx, expr const & e, unsigned fidx, unsigned num_fns, expr const & psum_type);

void initialize_pack_mutual();
void finalize_pack_mutual();
}
