/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/io_state.h"
#include "library/if_then_else_decls.h"

namespace lean {
expr mk_ite_fn();
bool is_ite_fn(expr const & e);
inline expr mk_ite(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app(mk_ite_fn(), e1, e2, e3, e4); }
void import_ite(environment const & env, io_state const & ios);
void open_ite(lua_State * L);
}
