/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/threadsafe_environment.h"

namespace lean {
void open_kernel_module(lua_State * L);
void register_kernel_module();
UDATA_DEFS(level)
UDATA_DEFS(local_entry)
UDATA_DEFS_CORE(local_context)
UDATA_DEFS(expr);
UDATA_DEFS(context_entry)
UDATA_DEFS(context)
UDATA_DEFS(formatter)
UDATA_DEFS(object)
UDATA_DEFS(environment)
UDATA_DEFS(justification)
UDATA_DEFS(metavar_env)
expr & to_nonnull_expr(lua_State * L, int idx);
/**
   \brief Return the formatter object associated with the given Lua State.
   This procedure checks for options at:
   1- Lean state object associated with \c L
   2- Lua Registry associated with \c L
*/
formatter get_global_formatter(lua_State * L);
/**
   \brief Update the formatter object associated with the given Lua State.
   If \c L is associated with a Lean state object \c S, then we update the formatter of \c S.
   Otherwise, we update the registry of \c L.
*/
void set_global_formatter(lua_State * L, formatter const & fmt);
/**
   \brief Auxiliary class for setting the Lua registry of a Lua state
   with an environment object.
*/
class set_environment {
    lua_State * m_state;
public:
    set_environment(lua_State * L, environment & env);
    ~set_environment();
};

/**
   \brief Helper class for getting a read-only reference
   for an environment object on the Lua stack.
*/
class ro_environment : public read_only_environment {
public:
    ro_environment(lua_State * L, int idx);
    ro_environment(lua_State * L);
};

/**
   \brief Helper class for getting a read-write reference
   for an environment object on the Lua stack.
*/
class rw_environment : public read_write_environment {
public:
    rw_environment(lua_State * L, int idx);
    rw_environment(lua_State * L);
};
}
