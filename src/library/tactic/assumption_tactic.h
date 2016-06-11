/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"

namespace lean {
optional<tactic_state> assumption(tactic_state const & s);
void initialize_assumption_tactic();
void finalize_assumption_tactic();
}
