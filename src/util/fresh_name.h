/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"

namespace lean {
/** \brief Create a unique fresh name. This operation is thread-safe, and it guarantees the names are unique
    even when multiple threads are used and they are created using */
name mk_fresh_name();

/** \brief Create a unique fresh name prefixed with the given tag. The tag is used to mark the name.
    \pre tag.is_atomic() */
name mk_tagged_fresh_name(name const & tag);

/** \brief Return true iff \c n is tagged by atomic name \c tag */
bool is_tagged_by(name const & n, name const & tag);
}
