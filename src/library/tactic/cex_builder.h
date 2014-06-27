/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/lua.h"
#include "util/name.h"
#include "util/optional.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"

namespace lean {
/** \brief In Lean, a counter-example is encoded using an environment object. */
typedef environment counterexample;
typedef std::function<counterexample(name const &, optional<counterexample> const &, substitution const &)> cex_builder_fn;
/** \brief Return a counterexample builder that expects a counterexample for the given goal. */
cex_builder_fn mk_cex_builder_for(name const & gname);

/** \brief Convert a Lua function on position \c idx (on the Lua stack) to a cex_builder_fn */
cex_builder_fn to_cex_builder(lua_State * L, int idx);
}
