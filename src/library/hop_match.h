/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/expr.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief Matching for higher-order patterns. Return true iff \c t matches the higher-order pattern \c p.
   The substitution is stored in \c subst.

   \c subst is an assignment for the free variables occurring in \c p.

   The free variables occurring in \c t are treated as constants.

   We say non-free variables occurring in \c p and \c t are "locally bound".

   \c p is a higher-order pattern when in all applications in \c p
      1- A free variable is not the function OR
      2- A free variable is the function, but all other arguments are distinct locally bound variables.

   \pre \c subst must be big enough to store all free variables occurring in subst

   If an environment is provided, then a constant \c c matches a term \c t if
   \c c is definitionally equal to \c t.

   If name_subst is different from nullptr, then the procedure stores in name_subst
   a mapping for binder names. It maps the binder names used in the pattern \c p into
   the binder names used in \c t.
*/
bool hop_match(expr const & p, expr const & t, buffer<optional<expr>> & subst,
               optional<ro_environment> const & env = optional<ro_environment>(),
               name_map<name> * name_subst = nullptr);
void open_hop_match(lua_State * L);
}
