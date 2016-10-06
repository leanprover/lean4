/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/util.h"

namespace lean {
enum class reducible_status { Reducible, Semireducible, Irreducible };
/** \brief Mark the definition named \c n as reducible or not.

    The method throws an exception if \c n is
      - not a definition
      - a theorem
      - an opaque definition that was not defined in main module

    "Reducible" definitions can be freely unfolded by automation (i.e., elaborator, simplifier, etc).
    We should view it as a hint to automation.
*/
environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent);

reducible_status get_reducible_status(environment const & env, name const & n);

inline bool is_reducible(environment const & env, name const & n) { return get_reducible_status(env, n) == reducible_status::Reducible; }
inline bool is_semireducible(environment const & env, name const & n) { return get_reducible_status(env, n) == reducible_status::Semireducible; }

/* \brief Execute the given function for each declaration explicitly marked with a reducibility annotation */
void for_each_reducible(environment const & env, std::function<void(name const &, reducible_status)> const & fn);

/** \brief Create a predicate that returns true for all non reducible constants in \c env */
name_predicate mk_not_reducible_pred(environment const & env);
/** \brief Create a predicate that returns true for irreducible constants  in \c env */
name_predicate mk_irreducible_pred(environment const & env);

unsigned get_reducibility_fingerprint(environment const & env);

void initialize_reducible();
void finalize_reducible();
}
