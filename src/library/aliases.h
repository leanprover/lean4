/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "kernel/environment.h"

namespace lean {
/** \brief Add the alias \c a for \c e. */
environment add_expr_alias(environment const & env, name const & a, name const & e, bool overwrite = false);
/**
   \brief Add alias \c a for \c e, and also add it to all parent scopes
   until in a namespace scope.
*/
environment add_expr_alias_rec(environment const & env, name const & a, name const & e, bool overwrite = false);

/** \brief If \c t is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_expr_aliased(environment const & env, name const & t);

/** \brief Return expressions associated with the given alias. */
list<name> get_expr_aliases(environment const & env, name const & n);

/** \brief Remove aliases for `n`, the effect affects the current scope only. */
environment erase_expr_aliases(environment const & env, name const & n);

/**
    \brief Add the alias \c a for level \c l. An error is generated if the new alias shadows
    existing aliases and/or declarations. We don't have "choice" construct for universe
    levels.
*/
environment add_level_alias(environment const & env, name const & a, name const & l);

/** \brief If \c l is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_level_aliased(environment const & env, name const & l);

/** \brief Return the level associated with the given alias. */
optional<name> get_level_alias(environment const & env, name const & n);

/**
   \brief Create an alias for each declaration named <tt>prefix.rest</tt>.
   The alias for <tt>prefix.rest</tt> is <tt>new_prefix.rest</tt>.

   \remark \c new_prefix may be the anonymous name.
*/
environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions = 0, name const * exceptions = nullptr, bool overwrite = false);
inline environment overwrite_aliases(environment const & env, name const & prefix, name const & new_prefix) {
    return add_aliases(env, prefix, new_prefix, 0, nullptr, true);
}

bool is_exception(name const & n, name const & prefix, unsigned num_exceptions, name const * exceptions);

void for_each_expr_alias(environment const & env, std::function<void(name const &, list<name> const &)> const & fn);

/* When we declare a definition in a section, we create an alias for it that fixes the parameters in
   universe parameters. */
environment add_local_ref(environment const & env, name const & a, expr const & ref);

optional<expr> get_local_ref(environment const & env, name const & n);

void initialize_aliases();
void finalize_aliases();
}
