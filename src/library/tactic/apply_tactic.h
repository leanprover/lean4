/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"
namespace lean {
tactic apply_tactic(expr const & th);
tactic apply_tactic(expr const & th, expr const & th_type);
tactic apply_tactic(name const & th_name);
void open_apply_tactic(lua_State * L);
}
