/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "util/optional.h"

namespace lean {
// =======================================
// Utilities for simulating Python-like named parameters using Lua tables.
// In the following function \c idx is the position of the Lua table on the Lua stack.
bool get_bool_named_param(lua_State * L, int idx, char const * opt_name, bool def_value);
int get_int_named_param(lua_State * L, int idx, char const * opt_name, int def_value);
unsigned get_uint_named_param(lua_State * L, int idx, char const * opt_name, unsigned def_value);
}
