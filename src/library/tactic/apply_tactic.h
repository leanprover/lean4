/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "library/tactic/tactic.h"
namespace lean {
tactic apply_tactic(elaborate_fn const & fn, expr const & e, bool relax_main_opaque = true);
tactic eassumption_tactic(bool relax_main_opaque = true);
void open_apply_tactic(lua_State * L);
expr mk_apply_tactic_macro(expr const & e);
void initialize_apply_tactic();
void finalize_apply_tactic();
}
