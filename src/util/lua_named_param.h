/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "util/optional.h"
#include "util/name_set.h"

namespace lean {
// =======================================
// Utilities for simulating Python-like named parameters using Lua tables.
// In the following function \c idx is the position of the Lua table on the Lua stack.
bool get_bool_named_param(lua_State * L, int idx, char const * opt_name, bool def_value);
int get_int_named_param(lua_State * L, int idx, char const * opt_name, int def_value);
unsigned get_uint_named_param(lua_State * L, int idx, char const * opt_name, unsigned def_value);
optional<unsigned> get_opt_uint_named_param(lua_State * L, int idx, char const * opt_name,
                                            optional<unsigned> const & def_value = optional<unsigned>());
name_set get_name_set_named_param(lua_State * L, int idx, char const * opt_name, name_set const & def_value = name_set());
list<name> get_list_name_named_param(lua_State * L, int idx, char const * opt_name, list<name> const & def_value);
}
