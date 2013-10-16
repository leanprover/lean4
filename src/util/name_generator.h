/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"

namespace lean {
/**
   \brief A generator of unique names modulo a prefix.
   If the prefix is unique (i.e., it is not the prefix of any other name in the system), then
   all generated names are unique.
*/
class name_generator {
    name     m_prefix;
    unsigned m_next_idx;
public:
    name_generator(name const & prefix):m_prefix(prefix), m_next_idx(0) { lean_assert(!prefix.is_anonymous()); }

    name const & prefix() const { return m_prefix; }

    /** \brief Return a unique name modulo \c prefix. */
    name next() { name r(m_prefix, m_next_idx); m_next_idx++; return r; }

    friend void swap(name_generator & a, name_generator & b) {
        swap(a.m_prefix, b.m_prefix);
        std::swap(a.m_next_idx, b.m_next_idx);
    }
};
}
