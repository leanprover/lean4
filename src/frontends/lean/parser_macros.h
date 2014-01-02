/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "frontends/lean/parser_types.h"
namespace lean {
macros & get_expr_macros(lua_State * L);
macros & get_tactic_macros(lua_State * L);
macros & get_cmd_macros(lua_State * L);
}
