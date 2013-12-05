/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"
namespace lean {
tactic conj_tactic(bool all = true);
tactic conj_hyp_tactic(bool all = true);
tactic imp_tactic(name const & H_name = name("H"), bool all = true);
tactic disj_hyp_tactic(name const & goal_name, name const & hyp_name);
tactic disj_hyp_tactic(name const & hyp_name);
tactic disj_hyp_tactic();
tactic disj_tactic();
tactic disj_tactic(unsigned i);
tactic disj_tactic(name const & gname);
tactic absurd_tactic();
void open_boolean(lua_State * L);
}
