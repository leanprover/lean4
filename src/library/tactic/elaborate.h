/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/metavar_context.h"

namespace lean {
expr mk_by(expr const & e);
bool is_by(expr const & e);
expr const & get_by_arg(expr const & e);

void initialize_elaborate();
void finalize_elaborate();
}
