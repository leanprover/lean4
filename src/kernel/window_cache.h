/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <new>
#include <utility>

namespace lean {
/* A cache in the hash table `Table` that keeps entries seen once only in a bounded window, and
   entries that were looked up again, or inserted again after leaving the window, without bound.
   The window holds two generations of at most `limit` entries each, like `two_gen_cache`. Keys
   inserted before are remembered by their hash only, so a result computed once and never needed
   again does not stay alive, while each result is computed at most twice. A hash collision merely
   moves an entry into the unbounded table early. */
template<typename Table>
class window_cache {
public:
    typedef typename Table::key_type   key_type;
    typedef typename Table::value_type value_type;
private:
    Table      m_hot;
    // window generation `m_new` and the older one `1 - m_new`
    Table      m_window[2];
    unsigned   m_new = 0;
    size_t     m_limit;
    // open addressing set of the nonzero hashes of all keys inserted so far
    uint64_t * m_seen = nullptr;
    size_t     m_seen_mask = 0;
    size_t     m_seen_size = 0;

    static uint64_t mix(uint64_t h) {
        h *= 0xBF58476D1CE4E5B9ull;
        h ^= h >> 31;
        return h ? h : 1;
    }
    void grow_seen() {
        size_t old_cap = m_seen ? m_seen_mask + 1 : 0;
        size_t cap = old_cap ? 2 * old_cap : 1024;
        uint64_t * seen = static_cast<uint64_t *>(std::calloc(cap, sizeof(uint64_t)));
        if (!seen)
            throw std::bad_alloc();
        for (size_t i = 0; i < old_cap; i++) {
            if (uint64_t h = m_seen[i]) {
                size_t j = h & (cap - 1);
                while (seen[j])
                    j = (j + 1) & (cap - 1);
                seen[j] = h;
            }
        }
        std::free(m_seen);
        m_seen = seen;
        m_seen_mask = cap - 1;
    }
    /* Records `h`, returning whether it was recorded before. */
    bool seen_before(uint64_t h) {
        if (!m_seen || 2 * (m_seen_size + 1) > m_seen_mask + 1)
            grow_seen();
        size_t i = h & m_seen_mask;
        while (uint64_t g = m_seen[i]) {
            if (g == h)
                return true;
            i = (i + 1) & m_seen_mask;
        }
        m_seen[i] = h;
        m_seen_size++;
        return false;
    }
    value_type const * promote(Table & gen, typename Table::iterator it) {
        value_type v = *it;
        gen.erase(it);
        return &*m_hot.insert(std::move(v)).first;
    }
public:
    explicit window_cache(size_t limit):m_limit(limit) {}
    window_cache(window_cache const &) = delete;
    ~window_cache() { std::free(m_seen); }
    /* The entry for `k`, or `nullptr`; valid until the next `find` or `insert`. */
    value_type const * find(key_type const & k) {
        auto it = m_hot.find(k);
        if (it != m_hot.end())
            return &*it;
        for (unsigned g : {m_new, 1 - m_new}) {
            Table & gen = m_window[g];
            if (gen.empty())
                continue;
            auto it_w = gen.find(k);
            if (it_w != gen.end())
                return promote(gen, it_w);
        }
        return nullptr;
    }
    template<typename V>
    void insert(V && v) {
        if (seen_before(mix(m_hot.hash_function()(v.first)))) {
            m_hot.insert(std::forward<V>(v));
            return;
        }
        if (m_window[m_new].size() >= m_limit) {
            m_new = 1 - m_new;
            // keeps the bucket array of the dropped generation
            m_window[m_new].clear();
        }
        m_window[m_new].insert(std::forward<V>(v));
    }
};
}
