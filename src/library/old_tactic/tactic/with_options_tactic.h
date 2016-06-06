/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_with_options_tactic_expr(options const & o, expr const & t);
void initialize_with_options_tactic();
void finalize_with_options_tactic();
}
