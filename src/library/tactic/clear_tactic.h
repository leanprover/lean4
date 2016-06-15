/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
namespace lean {
vm_obj clear(name const & n, tactic_state const & s, bool internal_name);
inline vm_obj clear_internal(name const & n, tactic_state const & s) { return clear(n, s, true); }
void initialize_clear_tactic();
void finalize_clear_tactic();
}
