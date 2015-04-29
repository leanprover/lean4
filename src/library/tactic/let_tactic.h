/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_let_tactic_expr(name const & id, expr const & e);
void initialize_let_tactic();
void finalize_let_tactic();
}
