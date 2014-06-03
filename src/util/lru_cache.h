/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include <algorithm>
#include <functional>
#include "util/debug.h"

namespace lean {
/** \brief Simple LRU cache on top of std::unordered_set */
template<typename Key, typename Hash = std::hash<Key>, typename Eq = std::equal_to<Key>>
class lru_cache {
    struct clist {
        clist * m_prev;
        clist * m_next;

        clist():m_prev(nullptr), m_next(nullptr) {}
        clist(clist * p, clist * n):m_prev(p), m_next(n) {}

        void remove() {
            m_prev->m_next = m_next;
            m_next->m_prev = m_prev;
        }

        void move_front(clist & head) {
            remove();
            m_prev              = &head;
            m_next              = head.m_next;
            head.m_next->m_prev = this;
            head.m_next         = this;
        }
    };

    struct entry : public clist {
        Key m_key;
        explicit entry(Key const & k):m_key(k) {}
        entry(Key const & k, clist & head):clist(&head, head.m_next), m_key(k) {
            head.m_next->m_prev = this;
            head.m_next         = this;
        }
        // Delete the copy and move constructors.
        // So, we get a compilation error if std::unordered_set tries
        // to copy entries. An entry object cannot be copied because
        // the m_prev, and m_next will not be correct.
        entry(entry && s)      = delete;
        entry(entry const & s) = delete;
    };

    struct entry_hash : private Hash {
        entry_hash(Hash const & h):Hash(h) {}
        std::size_t operator()(entry const & e) const { return Hash::operator()(e.m_key); }
    };

    struct entry_eq : private Eq {
        entry_eq(Eq const & e):Eq(e) {}
        bool operator()(entry const & e1, entry const & e2) const {
            return Eq::operator()(e1.m_key, e2.m_key);
        }
    };

    void remove_last() {
        lean_assert(m_cache.size() > 0);
        entry * last = static_cast<entry*>(m_head.m_prev);
        last->remove();
        m_cache.erase(entry(last->m_key));
    }

    unsigned                                        m_capacity;
    std::unordered_set<entry, entry_hash, entry_eq> m_cache;
    clist                                           m_head;
public:
    lru_cache(unsigned c, Hash const & h = Hash(), Eq const & e = Eq()):
        m_capacity(std::max(c, 1u)), m_cache(c, entry_hash(h), entry_eq(e)), m_head(&m_head, &m_head) {
    }

    /**
        \brief Insert key in the cache.
        If the chache alreayd contains an equivalent key, then return a pointer to it.
        Otherwise return nullptr.
    */
    Key const * insert(Key const & k) {
        auto it = m_cache.find(entry(k));
        if (it != m_cache.end()) {
            const_cast<entry &>(*it).move_front(m_head);
            return &it->m_key;
        } else {
            // We must use emplace to instead of insert, to avoid the copy constructor.
            m_cache.emplace(k, m_head);
            if (m_cache.size() > m_capacity)
                remove_last();
            return nullptr;
        }
    }

    /**
       \brief If this cache contains a key equivalent to \c k, then return it.
       Otherwise return nullptr. The key is moved to beginning of the queue.
    */
    Key const * find(Key const & k) {
        auto it = m_cache.find(entry(k));
        if (it != m_cache.end()) {
            const_cast<entry &>(*it).move_front(m_head);
            return &it->m_key;
        } else {
            return nullptr;
        }
    }

    /** \brief Remove the given key from the cache. */
    void erase(Key const & k) {
        auto it = m_cache.find(entry(k));
        if (it != m_cache.end()) {
            const_cast<entry &>(*it).remove();
            m_cache.erase(it);
        }
    }

    /** \brief Modify the capacity of this cache */
    void set_capacity(unsigned c) {
        m_capacity = std::max(c, 1u);
        while (m_cache.size() > m_capacity)
            remove_last();
    }

    /** \brief Remove all elements. */
    void clear() { m_cache.clear(); }
    /** \brief Return true iff the cache contains the given key. */
    bool contains(Key const & k) { return find(k); }
    /** \brief Return the number of elements stored in the cache. */
    unsigned size() const { return m_cache.size(); }
    /** \brief Return the capacity of this cache. */
    unsigned capacity() const { return m_capacity; }
    /** \brief Return true iff the cache is empty. */
    bool empty() const { return size() == 0; }
};
}
