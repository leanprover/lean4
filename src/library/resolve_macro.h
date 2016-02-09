/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_resolve_macro(expr const & l, expr const & H1, expr const & H2);
void initialize_resolve_macro();
void finalize_resolve_macro();
}
