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
}
