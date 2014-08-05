/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/lua.h"
#include "util/optional.h"
#include "util/buffer.h"
#include "util/name_map.h"
#include "kernel/expr.h"
#include "kernel/environment.h"

namespace lean {
/** \brief Callback for extending the higher-order pattern matching procedure.
    It is invoked before the matcher fails.

    plugin(p, t, s) must return true iff for updated substitution s', s'(p) is definitionally equal to t.
*/
typedef std::function<bool(expr const &, expr const &, buffer<optional<expr>> &, name_generator const &)> matcher_plugin; // NOLINT

/**
   \brief Matching for higher-order patterns. Return true iff \c t matches the higher-order pattern \c p.
   The substitution is stored in \c subst. Note that, this procedure treats free-variables as placholders
   instead of meta-variables.

   \c subst is an assignment for the free variables occurring in \c p.

   \pre \c t must not contain free variables. If it does, they must be replaced with local constants
   before invoking this functions.

   \c p is a higher-order pattern when in all applications in \c p
      1- A free variable is not the function OR
      2- A free variable is the function, but all other arguments are distinct local constants.

   \pre \c subst must be big enough to store all free variables occurring in subst

   If prefix is provided, then it is used for creating unique names.

   If name_subst is different from nullptr, then the procedure stores in name_subst
   a mapping for binder names. It maps the binder names used in the pattern \c p into
   the binder names used in \c t.

   If the plugin is provided, then it is invoked before a failure.
*/
bool match(expr const & p, expr const & t, buffer<optional<expr>> & subst, name const * prefix = nullptr,
               name_map<name> * name_subst = nullptr, matcher_plugin const * plugin = nullptr);
void open_match(lua_State * L);
}
