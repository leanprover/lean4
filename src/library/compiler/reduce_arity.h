/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/procedure.h"
#include "library/abstract_context_cache.h"

namespace lean {
/** \brief Try to reduce the arity of auxiliary declarations in procs.
    It assumes all but the last entry are auxiliary declarations.

    \remark This procedure assumes rec_fn_macro has already been eliminated.
    The procedure erase_irrelevant can be used to accomplish that.

    \remark This step does not rely on type information. That is,
    the input expressions don't need to be type checkable. */
void reduce_arity(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs);
}
