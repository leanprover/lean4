/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/proof_state.h"

namespace lean {
expr mk_info_tactic_expr();
/** \brief The tactic framework does not have access to the info manager.
    Thus, it cannot store the proof_state there. The info tactic accomplishes
    that by (temporarily) saving the proof state in a thread-local storage
    that is accessed by the elaborator using this function. */
optional<proof_state> get_info_tactic_proof_state();
void initialize_info_tactic();
void finalize_info_tactic();
}
