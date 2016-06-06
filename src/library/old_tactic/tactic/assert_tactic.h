/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
expr mk_assert_tactic_expr(name const & id, expr const & e);
tactic assert_tactic(elaborate_fn const & elab, name const & id, expr const & e);
void initialize_assert_tactic();
void finalize_assert_tactic();
}
