/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
namespace lean {
class environment;
class ro_environment;
class name;
/**
   \brief Return true iff the definition named \c d is hidden in
   the given environment.

   This information is just a hint used by tactics and solvers.  For
   example, unfold_tactic uses it to decide whether a definition
   should be unfolded or not.
*/
bool is_hidden(ro_environment const & env, name const & d);
/**
   \brief Mark the definition named \c d as hidden in the given environment.

   \see is_hidden

   \remark It throws an exception if \c d is not a definition in \c env.
*/
void set_hidden_flag(environment const & env, name const & d, bool flag = true);
/**
   \brief Hide definitions at builtin.cpp. We hide them here because
   the hidden_defs module is not part of the kernel.
*/
void hide_builtin(environment const & env);

void open_hidden_defs(lua_State * L);
}
