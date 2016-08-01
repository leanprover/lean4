/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
class expr;
// =======================================
// Structural equality
/** \brief Binder information is ignored in the following predicate */
bool is_equal(expr const & a, expr const & b);
inline bool operator==(expr const & a, expr const & b) { return is_equal(a, b); }
inline bool operator!=(expr const & a, expr const & b) { return !operator==(a, b); }
// =======================================

/** \brief Similar to ==, but it also compares binder information */
bool is_bi_equal(expr const & a, expr const & b);
struct is_bi_equal_proc { bool operator()(expr const & e1, expr const & e2) const { return is_bi_equal(e1, e2); } };

/** Similar to is_bi_equal_proc, but it has a flag that allows us to switch select == or is_bi_equal */
struct is_cond_bi_equal_proc {
    bool m_use_bi;
    is_cond_bi_equal_proc(bool b):m_use_bi(b) {}
    bool operator()(expr const & e1, expr const & e2) const { return m_use_bi ? is_bi_equal(e1, e2) : e1 == e2; }
};
}
