/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
namespace lean {
optional<tactic_state> intron(unsigned n, tactic_state const & s, buffer<name> & new_Hs);
optional<tactic_state> intron(unsigned n, tactic_state const & s);
void initialize_intro_tactic();
void finalize_intro_tactic();
}
