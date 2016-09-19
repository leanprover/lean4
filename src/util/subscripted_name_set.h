/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <limits>
#include "util/name_map.h"
#include "util/name_set.h"
#include "util/name.h"
namespace lean {
/**
 * \brief Set of names with an efficient operation to get unused names.
 */
class subscripted_name_set {
    name_set m_names;

    // For each subscripted name of the form prefix.append_after(idx), we keep track of
    // the indices that are not yet used.  The unused indices form a subset of the positive
    // natural numbers, this subset is stored as an rb_tree of intervals.
    struct closed_ival {
        unsigned begin, end;
        closed_ival() : begin(1), end(std::numeric_limits<unsigned>::max()) {}
        closed_ival(unsigned singleton) : begin(singleton), end(singleton) {}
        closed_ival(unsigned begin, unsigned end) : begin(begin), end(end) {}
        bool contains(unsigned i) const { return begin <= i && i <= end; }
    };
    struct closed_ival_cmp {
        int operator()(closed_ival const & i1, closed_ival const & i2) const {
            return unsigned_cmp()(i1.end, i2.end);
        }
    };
    typedef rb_tree<closed_ival, closed_ival_cmp> free_subscript_set;
    name_map<free_subscript_set> m_prefixes;

    void check_invariants() const;

public:
    subscripted_name_set() : m_names(), m_prefixes() {}

    bool contains(name const & n) const { return m_names.contains(n); }
    void insert(name const & n);
    void erase(name const & n);

    name get_unused_name(name const & suggestion) const;
    name get_unused_name(name const & prefix, unsigned idx) const;
};
}
