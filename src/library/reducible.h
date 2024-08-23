/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/util.h"
#include "library/elab_environment.h"

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
elab_environment set_reducible(elab_environment const & env, name const & n, reducible_status s, bool persistent);

reducible_status get_reducible_status(elab_environment const & env, name const & n);

inline bool is_reducible(elab_environment const & env, name const & n) { return get_reducible_status(env, n) == reducible_status::Reducible; }
inline bool is_semireducible(elab_environment const & env, name const & n) { return get_reducible_status(env, n) == reducible_status::Semireducible; }
}
