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

    friend name_generator to_name_generator(obj_arg o);
    friend object_ref to_obj(name_generator const &);
public:
    name_generator();
    /* Create a name generator with the given prefix.
       The prefix should start with a name registered using \c register_name_generator_prefix.

       \pre uses_name_generator_prefix(prefix) */
    explicit name_generator(name const & prefix);

    name const & prefix() const { return m_prefix; }

    /** \brief Return a unique name modulo \c prefix. */
    name next();

    /**
       \brief Similar to \c next, but the base prefix is replaced with the given one.

       \pre \c base_prefix must have been registered using \c register_name_generator_prefix.

       Example: suppose `_cfresh` and `_ffresh` have been registered using \c register_name_generator_prefix,
       and the current state is `m_prefix == _ffresh.2` and `m_next_idx = 10`. Then, the name
       returned by `next_with(_cfresh)` is `_cfresh.2.10`, and
       the current state of this object is updated to `m_next_idx = 11` */
    name next_with(name const & base_prefix);

    /**
        \brief Create a child name_generator, each child name_generator is guaranteed to produce
        names different from this name_generator and any other name_generator created with this generator. */
    name_generator mk_child() { return name_generator(next()); }

    /**
       \brief Similar to \c mk_child, but the base prefix is replaced with the given one.

       \pre \c base_prefix must have been registered using \c register_name_generator_prefix.

       Example: suppose `_cfresh` and `_ffresh` have been registered using \c register_name_generator_prefix,
       and the current state is `m_prefix == _ffresh.2` and `m_next_idx = 10`. Then, the name_generator
       returned by `mk_child_with(_cfresh)` is `{m_prefix = _cfresh.2.10, m_next_idx = 0}`, and
       the current state of this object is updated to `m_next_idx = 11` */
    name_generator mk_child_with(name const & base_prefix) { return name_generator(next_with(base_prefix)); }

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
