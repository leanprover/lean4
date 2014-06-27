/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include "util/lua.h"
#include "util/name.h"
#include "util/rb_map.h"
#include "kernel/expr.h"

namespace lean {
typedef rb_map<name, expr, name_quick_cmp> proof_map;
/**
   \brief Return the proof (of inhabitated type) for the goal named \c n in the \c proof_map \c m.
   Throw an exception if \c m does not contain a proof for \c n.
*/
expr find(proof_map const & m, name const & n);
/**
   \brief A proof builder creates an inhabitant a goal type (aka
   conclusion) using the inhabitants for its subgoals.
*/
typedef std::function<expr(proof_map const &, substitution const &)> proof_builder_fn;
proof_builder_fn add_proofs(proof_builder_fn const & pb, list<std::pair<name, expr>> const & prs);

/** \brief Convert a Lua function on position \c idx (on the Lua stack) into a proof_builder_fn */
proof_builder_fn to_proof_builder(lua_State * L, int idx);
UDATA_DEFS_CORE(proof_map)
void open_proof_builder(lua_State * L);
}
