/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/lua.h"
#include "kernel/environment.h"

namespace lean {
/** \brief Add the alias \c a for expression \c e. \c e must not have free variables. */
environment add_alias(environment const & env, name const & a, expr const & e);
/**
   \brief Add alias \c a for expression \c e, and also add it to all parent scopes
   until in a namespace scope.
*/
environment add_decl_alias(environment const & env, name const & a, expr const & e);

/** \brief If \c t is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_aliased(environment const & env, expr const & t);

/** \brief Return expressions associated with the given alias. */
list<expr> get_alias_exprs(environment const & env, name const & n);

/**
    \brief Add the alias \c a for the level expression \c l. An error is generated if the new alias shadows
    existing aliases and/or declarations. We don't have "choice" construct for universe
    levels.
*/
environment add_alias(environment const & env, name const & a, level const & l);

/** \brief If \c l is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_aliased(environment const & env, level const & l);

/** \brief Return the level associated with the given alias. */
optional<level> get_alias_level(environment const & env, name const & n);

/**
   \brief Create an alias for each declaration named <tt>prefix.rest</tt>.
   The alias for <tt>prefix.rest</tt> is <tt>new_prefix.rest</tt>.

   The command will also create aliases for universe level declarations.
   However, an error is thrown if the universe level shadows existing aliases and/or declarations.
   We don't have "choice" construct for universe levels.

   \remark \c new_prefix may be the anonymous name.
*/
environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions = 0, name const * exceptions = nullptr);

void open_aliases(lua_State * L);
}
