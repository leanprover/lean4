/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/optional.h"
#include "library/substitution.h"

namespace lean {
optional<substitution> fo_unify(expr e1, expr e2);
void open_fo_unify(lua_State * L);
}
