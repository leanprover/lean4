/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <limits>
#include <iostream>
#include "library/subscripted_name_set.h"

namespace lean {
void subscripted_name_set::check_invariants() const {
    m_names.for_each([&] (name const & n) {
       if (auto is_subscripted = n.is_subscripted()) {
           auto subscripts = m_prefixes.find(is_subscripted->first);
           lean_assert(subscripts);
           DEBUG_CODE(auto free_region =) subscripts->find_next_greater_or_equal(closed_ival(is_subscripted->second));
           lean_assert(free_region);
           lean_assert(!free_region->contains(is_subscripted->second));
       }
    });
    m_prefixes.for_each([&] (name const &, free_subscript_set const & subscripts) {
        unsigned last_end = 0;
        subscripts.for_each([&] (closed_ival const & region) {
            lean_assert(last_end < region.begin);
            lean_assert(region.begin <= region.end);
            last_end = region.end;
        });
        lean_assert(last_end == std::numeric_limits<unsigned>::max());
    });
}

void subscripted_name_set::insert(name const & n) {
    if (contains(n)) return;
    m_names.insert(n);
    if (auto is_subscripted = n.is_subscripted()) {
        free_subscript_set subscripts;
        if (auto entry = m_prefixes.find(is_subscripted->first)) {
            subscripts = *entry;
        } else {
            subscripts.insert(closed_ival());
        }
        unsigned idx = is_subscripted->second;
        closed_ival free_region = *subscripts.find_next_greater_or_equal(closed_ival(idx));
        if (free_region.contains(idx)) {
            subscripts.erase(free_region);
            if (free_region.begin < idx)
                subscripts.insert(closed_ival(free_region.begin, idx - 1));
            if (idx < free_region.end)
                subscripts.insert(closed_ival(idx + 1, free_region.end));
        }
        m_prefixes.insert(is_subscripted->first, subscripts);
    }
    DEBUG_CODE(check_invariants());
}

void subscripted_name_set::erase(name const & n) {
    if (!contains(n)) return;
    m_names.erase(n);
    if (auto is_subscripted = n.is_subscripted()) {
        unsigned idx = is_subscripted->second;
        free_subscript_set subscripts = *m_prefixes.find(is_subscripted->first);
        auto prev_free_region = *subscripts.find_next_greater_or_equal(closed_ival(idx - 1));
        auto next_free_region = *subscripts.find_next_greater_or_equal(closed_ival(idx));

        if (prev_free_region.end == next_free_region.end) {
            if (next_free_region.begin == idx + 1) {
                subscripts.insert(closed_ival(idx, next_free_region.end));  // replaces next_free_region
            } else {
                lean_assert(next_free_region.begin > idx + 1);
                subscripts.insert(closed_ival(idx));
            }
        } else {
            lean_assert(prev_free_region.end == idx - 1);
            if (next_free_region.begin == idx + 1) {
                subscripts.erase(prev_free_region);
                subscripts.insert(closed_ival(prev_free_region.begin, next_free_region.end)); // replaces next_free_region
            } else {
                lean_assert(next_free_region.begin > idx + 1);
                subscripts.erase(prev_free_region);
                subscripts.insert(closed_ival(prev_free_region.begin, idx));
            }
        }

        m_prefixes.insert(is_subscripted->first, subscripts);
    }
    DEBUG_CODE(check_invariants());
}

name subscripted_name_set::get_unused_name(name const & prefix, unsigned idx) const {
    if (auto free_subscripts = m_prefixes.find(prefix.get_subscript_base())) {
        auto free_region = free_subscripts->find_next_greater_or_equal(closed_ival(idx));
        if (free_region->begin >= idx)
            idx = free_region->begin;
    }
    name n = prefix.append_after(idx);
    lean_assert(!contains(n));
    return n;
}

name subscripted_name_set::get_unused_name(name const & suggestion) const {
    if (!contains(suggestion))
        return suggestion;
    return get_unused_name(suggestion, 1);
}
}
