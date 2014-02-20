/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/name.h"

namespace lean {
/**
   \brief A generator of unique names modulo a prefix.
   If the initial prefix is independent of all other names in the system, then all generated names are unique.

   \remark There is no risk of overflow in the m_next_idx. If m_next_idx reaches std::numeric_limits<unsigned>::max(),
   then the prefix becomes name(m_prefix, m_next_idx), and m_next_idx is reset to 0
*/
class name_generator {
    name     m_prefix;
    unsigned m_next_idx;
public:
    name_generator(name const & prefix):m_prefix(prefix), m_next_idx(0) { lean_assert(!prefix.is_anonymous()); }

    name const & prefix() const { return m_prefix; }

    /** \brief Return a unique name modulo \c prefix. */
    name next();

    /**
        \brief Create a child name_generator, each child name_generator is guaranteed to produce
        names different from this name_generator and any other name_generator created with this generator.
    */
    name_generator mk_child() { return name_generator(next()); }

    friend void swap(name_generator & a, name_generator & b);
};
void swap(name_generator & a, name_generator & b);
}
