/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "library/tactic/elaborate.h"
namespace lean {
proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s, expr const & e, constraint_seq const & cs);
proof_state_seq fapply_tactic_core(environment const & env, io_state const & ios, proof_state const & s, expr const & e, constraint_seq const & cs);
tactic apply_tactic_core(expr const & e, constraint_seq const & cs = constraint_seq());
tactic apply_tactic(elaborate_fn const & fn, expr const & e);
tactic fapply_tactic(elaborate_fn const & fn, expr const & e);
tactic eassumption_tactic();
tactic assumption_tactic();
void initialize_apply_tactic();
void finalize_apply_tactic();
}
