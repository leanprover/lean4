/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/lua.h"
#include "kernel/environment.h"
#include "library/io_state.h"

namespace lean {
/**
    \brief Add the alias \c a for expression \c e. \c e must not have
    free variables. Warning messages are generated if the new alias shadows
    existing aliases and/or declarations.
*/
environment add_alias(environment const & env, name const & a, expr const & e, io_state const & ios);
/**
   \brief Create an alias for each declaration named <tt>prefix.rest</tt>.
   The alias for <tt>prefix.rest</tt> is <tt>new_prefix.rest</tt>.
   Warning messages are generated if the new aliases shadow existing aliases and/or declarations.

   \remark \c new_prefix may be the anonymous name.
*/
environment add_aliases(environment const & env, name const & prefix, name const & new_prefix, io_state const & ios);
/**
   \brief Create an alias for each declaration named <tt>prefix.rest</tt>, the alias will also fix the value of parameters
   in \c fix_params. The argument \c fix_params is a sequence of pairs <tt>(name, expr)</tt>, where the \c name is the
   name of the parameter to be fixed.
   Warning messages are generated if the new aliases shadow existing aliases and/or declarations.
*/
environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_fix_params, std::pair<name, expr> const * fix_params, io_state const & ios);

/** \brief If \c t is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_aliased(environment const & env, expr const & t);

/** \brief Return expression associated with the given alias. */
optional<expr> get_alias(environment const & env, name const & n);

void open_aliases(lua_State * L);
}
