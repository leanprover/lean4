/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
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
    name_generator();

    name const & prefix() const { return m_prefix; }

    /** \brief Return a unique name modulo \c prefix. */
    name next();

    /**
        \brief Create a child name_generator, each child name_generator is guaranteed to produce
        names different from this name_generator and any other name_generator created with this generator.
    */
    name_generator mk_child() { return name_generator(next()); }

    name_generator mk_tagged_child(name const & prefix) { return name_generator(prefix + next()); }

    friend void swap(name_generator & a, name_generator & b);
};
void swap(name_generator & a, name_generator & b);

/* This procedure is invoked during initialization time to register
   internal prefixes used to create name_generator objects.

   The registration process has two benefits:
   1- Make sure two different modules do not use the same prefix.
      We get an assertion violation if more than one module uses the same prefix.

   2- The registered names are used to implement `uses_name_generator_prefix` and `sanitize_name_generator_name`
*/
void register_name_generator_prefix(name const & n);

/* Return true if \c n was generated using a prefix registered using \c register_name_generator_prefix */
bool uses_name_generator_prefix(name const & n);

/* If \c n was generated using a name_generator with a registered prefix, then
   make sure the result is a valid Lean name (i.e., it does not have numeric parts).
   Example: `sanitize_name_generator_name(_fresh.1.4)` returns `_fresh_1_4`. */
name sanitize_name_generator_name(name const & n);

void initialize_name_generator();
void finalize_name_generator();
}
