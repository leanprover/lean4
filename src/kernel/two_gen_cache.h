/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <cstddef>
#include <utility>

namespace lean {
/* A cache of at most `2 * limit` entries kept in two generations of the hash table `Table` (a map
   or a set), like `Lean.Meta.UnfoldCache`: entries are inserted into the new generation; when it
   reaches `limit` entries, it becomes the old generation and the previous old one is dropped. A hit
   in the old generation is copied back into the new one. */
template<typename Table>
class two_gen_cache {
public:
    typedef typename Table::key_type   key_type;
    typedef typename Table::value_type value_type;
private:
    // generation `m_new` and the older generation `1 - m_new`
    Table    m_gens[2];
    unsigned m_new = 0;
    size_t   m_limit;
public:
    explicit two_gen_cache(size_t limit):m_limit(limit) {}
    /* The entry for `k`, or `nullptr`; valid until the next `find` or `insert`. */
    value_type const * find(key_type const & k) {
        Table & new_gen = m_gens[m_new];
        auto it = new_gen.find(k);
        if (it != new_gen.end())
            return &*it;
        Table & old_gen = m_gens[1 - m_new];
        if (old_gen.empty())
            return nullptr;
        auto it_old = old_gen.find(k);
        if (it_old == old_gen.end())
            return nullptr;
        // copy first, as `insert` may drop the old generation
        value_type v = *it_old;
        return insert(std::move(v));
    }
    template<typename V>
    value_type const * insert(V && v) {
        if (m_gens[m_new].size() >= m_limit) {
            m_new = 1 - m_new;
            // keeps the bucket array of the dropped generation
            m_gens[m_new].clear();
        }
        return &*m_gens[m_new].insert(std::forward<V>(v)).first;
    }
};
}
