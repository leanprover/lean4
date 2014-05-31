/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "library/kernel_bindings.h"
#include "library/resolve_macro.h"
#include "library/coercion.h"
#include "library/private.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/scope.h"
// #include "library/fo_unify.h"
// #include "library/hop_match.h"

namespace lean {
inline void open_core_module(lua_State * L) {
    open_kernel_module(L);
    open_resolve_macro(L);
    open_coercion(L);
    open_private(L);
    open_placeholder(L);
    open_aliases(L);
    open_scope(L);
    // open_fo_unify(L);
    // open_hop_match(L);
}
inline void register_core_module() {
    script_state::register_module(open_core_module);
}
}
