/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/elaborate.h"

namespace lean {
expr mk_generalize_tactic_expr(expr const & e, name const & id);
optional<proof_state> generalize_core(environment const & env, io_state const & ios, elaborate_fn const & elab,
                                      expr const & e, name const & x, proof_state const & s, name const & tac_name,
                                      bool intro);
void initialize_generalize_tactic();
void finalize_generalize_tactic();
}
