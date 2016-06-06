/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/proof_state.h"
namespace lean {
optional<proof_state> subst(environment const & env, name const & h_name, bool symm, proof_state const & s);
void initialize_subst_tactic();
void finalize_subst_tactic();
}
