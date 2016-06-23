/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
/** \brief Return a hash code for \c e that ignores instance parameters
    (and proofs) in \c e.

    Example: the following two instances have the same hashcode
       (@add nat nat_has_add a b)
       (@add nat (add_monoid_has_add nat nat_is_monoid) a b) */
unsigned abstract_hash(type_context & ctx, expr const & e);
/** \brief Weight function that ignores the type class instances in \c e.  */
unsigned abstract_weight(type_context & ctx, expr const & e);
/** \brief Equality function that ignores type class instances. */
bool abstract_eq(type_context & ctx, expr const & e1, expr const & e2);
/** \brief Less than function that ignores type class instances. */
bool abstract_lt(type_context & ctx, expr const & e1, expr const & e2);
}
