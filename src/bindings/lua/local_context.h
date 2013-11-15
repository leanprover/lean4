/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
#include "kernel/expr.h"
namespace lean {
UDATA_DEFS(local_entry)
UDATA_DEFS_CORE(local_context)
void open_local_context(lua_State * L);
}
