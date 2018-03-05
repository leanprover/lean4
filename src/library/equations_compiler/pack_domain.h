/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** \brief Create a new equations object where all functions being defined are unary.
    The trick is to pack multiple arguments using a Sigma type. */
expr pack_domain(type_context_old & ctx, expr const & e);
}
