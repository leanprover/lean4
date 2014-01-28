/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "util/splay_map.h"
#include "util/name.h"
#include "kernel/expr.h"
#include "kernel/metavar.h"

namespace lean {
/**
   \brief Simpler version of metavar_env.
   It is used in fo_unify
*/
typedef splay_map<name, expr, name_quick_cmp> substitution;
/**
   \brief Apply substitution \c s to \c e
*/
expr apply(substitution & s, expr const & e, optional<ro_metavar_env> const & menv = none_ro_menv());
inline expr apply(substitution & s, expr const & e, ro_metavar_env const & menv) { return apply(s, e, some_ro_menv(menv)); }

expr find(substitution & s, expr e);
UDATA_DEFS_CORE(substitution)
void open_substitution(lua_State * L);
}
