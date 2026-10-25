/*
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdint>
#include <cstdlib>
#include <new>

namespace lean {
/* A set of pairs of a non-null pointer and a word, for the caches of traversals such as
   `expr_eq_fn` and `for_each_fn`. Open addressing, as `std::unordered_set` allocates a node per
   element. */
class ptr_pair_set {
    struct slot {
        void const * m_ptr; // `nullptr` if empty
        uintptr_t    m_word;
    };
    static constexpr size_t initial_capacity = 16;
    // Most traversals insert only a few elements, so the first slots need no allocation.
    slot   m_initial[initial_capacity] = {};
    slot * m_slots = m_initial;
    size_t m_mask  = initial_capacity - 1;
    size_t m_size  = 0;

    static size_t hash_of(void const * p, uintptr_t w) {
        uint64_t h = (reinterpret_cast<uint64_t>(p) >> 3) ^ (static_cast<uint64_t>(w) * 0x9E3779B97F4A7C15ull);
        h *= 0xBF58476D1CE4E5B9ull;
        return static_cast<size_t>(h ^ (h >> 31));
    }
    void grow() {
        slot * old = m_slots;
        size_t old_cap = m_mask + 1;
        size_t cap = 2 * old_cap;
        slot * slots = static_cast<slot *>(std::calloc(cap, sizeof(slot)));
        if (!slots)
            throw std::bad_alloc();
        m_slots = slots;
        m_mask = cap - 1;
        for (size_t i = 0; i < old_cap; i++) {
            if (old[i].m_ptr) {
                size_t j = hash_of(old[i].m_ptr, old[i].m_word) & m_mask;
                while (m_slots[j].m_ptr)
                    j = (j + 1) & m_mask;
                m_slots[j] = old[i];
            }
        }
        if (old != m_initial)
            std::free(old);
    }
public:
    ptr_pair_set() {}
    ptr_pair_set(ptr_pair_set const &) = delete;
    ~ptr_pair_set() {
        if (m_slots != m_initial)
            std::free(m_slots);
    }
    /* Inserts `(p, w)`, returning whether it was absent. */
    bool insert(void const * p, uintptr_t w) {
        if (2 * (m_size + 1) > m_mask + 1)
            grow();
        size_t i = hash_of(p, w) & m_mask;
        while (void const * q = m_slots[i].m_ptr) {
            if (q == p && m_slots[i].m_word == w)
                return false;
            i = (i + 1) & m_mask;
        }
        m_slots[i] = slot{p, w};
        m_size++;
        return true;
    }
};
}
