/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "library/tactic/tactic.h"
namespace lean {
tactic apply_tactic(expr const & e);
tactic eassumption_tactic();
void open_apply_tactic(lua_State * L);
}
