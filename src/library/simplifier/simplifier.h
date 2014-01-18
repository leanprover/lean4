/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/environment.h"
#include "library/expr_pair.h"

namespace lean {
expr_pair simplify(expr const & e, ro_environment const & env, context const & ctx, options const & opts);
void open_simplifier(lua_State * L);
}
