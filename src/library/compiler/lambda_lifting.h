/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/abstract_context_cache.h"
#include "library/compiler/procedure.h"
namespace lean {
/** \brief Lift lambda expressions in \c procs. New declarations are added to procs.
    \remark This procedure assumes erase_irrelevant was already applied. */
void lambda_lifting(environment const & env, abstract_context_cache & cache, name const & prefix, buffer<procedure> & procs);
};
