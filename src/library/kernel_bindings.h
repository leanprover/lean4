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
int push_environment(lua_State * L, ro_environment const & env);
int push_optional_expr(lua_State * L, optional<expr> const & e);
int push_optional_justification(lua_State * L, optional<justification> const & j);
int push_optional_object(lua_State * L, optional<object> const & o);
/**
   \brief Return the formatter object associated with the given Lua State.
   This procedure checks for options at:
   1- Lean state object associated with \c L
   2- Lua Registry associated with \c L
*/
optional<formatter> get_global_formatter_core(lua_State * L);
/**
   \brief Similar to \c get_global_formatter_core, but returns
   the simple_formatter if a formatter can't be found.
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
    set_environment(lua_State * L, environment const & env);
    ~set_environment();
};

/**
   \brief Helper class for getting a read-only reference
   for an environment object on the Lua stack.
*/
class ro_shared_environment : public read_only_shared_environment {
public:
    ro_shared_environment(lua_State * L, int idx);
    ro_shared_environment(lua_State * L);
};

/**
   \brief Helper class for getting a read-write reference
   for an environment object on the Lua stack.
*/
class rw_shared_environment : public read_write_shared_environment {
public:
    rw_shared_environment(lua_State * L, int idx);
    rw_shared_environment(lua_State * L);
};
}
