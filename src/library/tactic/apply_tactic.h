/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "library/tactic/elaborate.h"
namespace lean {
tactic apply_tactic(elaborate_fn const & fn, expr const & e);
tactic fapply_tactic(elaborate_fn const & fn, expr const & e);
tactic eassumption_tactic();
void open_apply_tactic(lua_State * L);
void initialize_apply_tactic();
void finalize_apply_tactic();
}
