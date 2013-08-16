/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "environment.h"

namespace lean {
/** \brief Initialize environment with builtin objects and basic theorems. */
void init_toplevel(environment & env);
/** \brief Create top-level environment with builtin objects and basic theorems. */
environment mk_toplevel();
}
