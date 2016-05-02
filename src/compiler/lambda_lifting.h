/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Lift lambda expressions in \c e. New declarations are added to new_decls,
    \remark The environment is also updated */
expr lambda_lifting(environment & env, expr const & e, buffer<name> & new_decls, bool trusted);
}
