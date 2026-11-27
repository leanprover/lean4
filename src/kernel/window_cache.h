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
   dropped from the window are remembered in a fixed-size Bloom filter, so a result computed once
   and never needed again does not stay alive, while each result is computed at most twice. A false
   positive of the filter merely moves an entry into the unbounded table early. */
template<typename Table>
class window_cache {
public:
    typedef typename Table::key_type   key_type;
    typedef typename Table::value_type value_type;
private:
    static constexpr unsigned filter_log_bits = 23;
    static constexpr unsigned filter_num_probes = 3;
    Table      m_hot;
    // window generation `m_new` and the older one `1 - m_new`
    Table      m_window[2];
    unsigned   m_new = 0;
    size_t     m_limit;
    // Bloom filter of the keys dropped from the window, allocated on the first drop
    uint64_t * m_filter = nullptr;

    uint64_t hash_of(key_type const & k) const {
        uint64_t h = static_cast<uint64_t>(m_hot.hash_function()(k));
        h *= 0xBF58476D1CE4E5B9ull;
        return h ^ (h >> 31);
    }
    /* The bit index of probe `i` for `h`, by double hashing. */
    static size_t probe(uint64_t h, unsigned i) {
        uint64_t h2 = (h >> 32) | 1;
        return static_cast<size_t>((h + i * h2) & ((static_cast<uint64_t>(1) << filter_log_bits) - 1));
    }
    bool filter_contains(uint64_t h) const {
        for (unsigned i = 0; i < filter_num_probes; i++) {
            size_t b = probe(h, i);
            if (!(m_filter[b / 64] & (static_cast<uint64_t>(1) << (b % 64))))
                return false;
        }
        return true;
    }
    void filter_add(uint64_t h) {
        for (unsigned i = 0; i < filter_num_probes; i++) {
            size_t b = probe(h, i);
            m_filter[b / 64] |= static_cast<uint64_t>(1) << (b % 64);
        }
    }
    void drop_oldest_generation() {
        Table & oldest = m_window[1 - m_new];
        if (!m_filter) {
            m_filter = static_cast<uint64_t *>(std::calloc((static_cast<size_t>(1) << filter_log_bits) / 64, sizeof(uint64_t)));
            if (!m_filter)
                throw std::bad_alloc();
        }
        for (value_type const & e : oldest)
            filter_add(hash_of(e.first));
        m_new = 1 - m_new;
        // keeps the bucket array of the dropped generation
        oldest.clear();
    }
    value_type const * promote(Table & gen, typename Table::iterator it) {
        value_type v = *it;
        gen.erase(it);
        return &*m_hot.insert(std::move(v)).first;
    }
public:
    explicit window_cache(size_t limit):m_limit(limit) {}
    window_cache(window_cache const &) = delete;
    ~window_cache() { std::free(m_filter); }
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
        // only keys dropped from the window can have been computed before
        if (m_filter && filter_contains(hash_of(v.first))) {
            m_hot.insert(std::forward<V>(v));
            return;
        }
        if (m_window[m_new].size() >= m_limit)
            drop_oldest_generation();
        m_window[m_new].insert(std::forward<V>(v));
    }
};
}
