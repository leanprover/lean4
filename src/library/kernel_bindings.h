/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"

namespace lean {
void open_kernel_module(lua_State * L);
UDATA_DEFS(level)
UDATA_DEFS(expr)
UDATA_DEFS(formatter)
UDATA_DEFS(definition)
UDATA_DEFS(macro_definition)
UDATA_DEFS(environment)
UDATA_DEFS(substitution)
UDATA_DEFS(justification)
UDATA_DEFS(constraint)
UDATA_DEFS_CORE(constraint_seq)
UDATA_DEFS(substitution)
UDATA_DEFS(io_state)
UDATA_DEFS_CORE(type_checker_ref)

int push_optional_level(lua_State * L, optional<level> const & e);
int push_optional_expr(lua_State * L, optional<expr> const & e);
int push_optional_justification(lua_State * L, optional<justification> const & j);
int push_optional_declaration(lua_State * L, optional<declaration> const & e);
int push_optional_constraint(lua_State * L, optional<constraint> const & c);
int push_list_expr(lua_State * L, list<expr> const & l);
/**
   \brief Return the formatter factory object associated with the given Lua State.
   This procedure checks for options at:
   1- Lean state object associated with \c L
   2- Lua Registry associated with \c L
*/
optional<formatter_factory> get_global_formatter_factory_core(lua_State * L);
/**
   \brief Similar to \c get_global_formatter_factory_core, but returns
   the simple_formatter if a formatter can't be found.
*/
formatter_factory get_global_formatter_factory(lua_State * L);
/**
   \brief Update the formatter object associated with the given Lua State.
   If \c L is associated with a Lean state object \c S, then we update the formatter of \c S.
   Otherwise, we update the registry of \c L.
*/
void set_global_formatter_factory(lua_State * L, formatter_factory const & fmtf);

/** \brief Make a fresh formatter object using the global formatter factory associated with L, and the global environment */
formatter mk_formatter(lua_State * L);

/** \brief Set the Lua registry of a Lua state with an environment object. */
void set_global_environment(lua_State * L, environment const & env);
environment get_global_environment(lua_State * L);
/**
   \brief Auxiliary class for temporarily setting the Lua registry of a Lua state
   with an environment object.
*/
class set_environment {
    lua_State *   m_state;
    environment * m_old_env;
public:
    set_environment(lua_State * L, environment & env);
    set_environment(script_state & S, environment & env):set_environment(S.get_state(), env) {}
    ~set_environment();
};

/** \brief Set the Lua registry of a Lua state with an io_state object. */
void set_global_io_state(lua_State * L, io_state & ios);
/**
   \brief Auxiliary class for temporarily setting the Lua registry of a Lua state
   with a Lean io_state object.
*/
class set_io_state {
    lua_State * m_state;
    io_state *  m_prev;
    options     m_prev_options;
public:
    set_io_state(lua_State * L, io_state & ios);
    set_io_state(script_state & S, io_state & ios):set_io_state(S.get_state(), ios) {}
    ~set_io_state();
};
/**
   \brief Return the Lean state object associated with the given Lua state.
   Return nullptr is there is none.
*/
io_state * get_io_state_ptr(lua_State * L);
io_state get_io_state(lua_State * L);
io_state to_io_state_ext(lua_State * L, int idx);
void open_io_state(lua_State * L);

void initialize_kernel_bindings();
void finalize_kernel_bindings();
}
