/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/tactic/tactic.h"
#include "library/simplifier/simplifier.h"
namespace lean {
tactic simplify_tactic(options const & opts, unsigned num_ns, name const * ns, std::shared_ptr<simplifier_monitor> const & monitor);
void open_simplify_tactic(lua_State * L);
}
