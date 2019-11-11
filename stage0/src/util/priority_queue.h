/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <limits>
#include "util/rb_map.h"

namespace lean {
/** \brief A "functional" priority queue, i.e., copy is O(1).
    If two keys have the same priority, then we break ties by
    giving higher priority to the last one added.
    The insert/erase operations are O(log n),
    where n is the size of the queue.
    The content of the queue can be dumped into a buffer or traversed */
template<typename K, typename CMP>
class priority_queue {
    typedef pair<unsigned, unsigned> pos;
    struct pos_cmp {
        int operator()(pos const & p1, pos const & p2) const {
            if (p1.first == p2.first)
                return p1.second == p2.second ? 0 : (p1.second > p2.second ? -1 : 1);
            else
                return p1.first > p2.first ? -1 : 1;
        }
    };
    unsigned                m_next{0};
    rb_map<K, pos, CMP>     m_key_to_pos;
    rb_map<pos, K, pos_cmp> m_pos_to_key;

    void normalize() {
        buffer<K> ks;
        to_buffer(ks);
        clear();
        for (K const & k : ks)
            insert(k);
    }

public:
    priority_queue(CMP const & cmp = CMP()):m_key_to_pos(cmp) {}

    template<typename F>
    void for_each(F && f) const {
        m_pos_to_key.for_each([&](pos const &, K const & k) {
                f(k);
            });
    }

    void to_buffer(buffer<K> & r) const {
        for_each([&](K const & k) { r.push_back(k); });
    }

    bool contains(K const & k) const {
        return m_key_to_pos.contains(k);
    }

    optional<unsigned> get_prio(K const & k) const {
        if (auto p = m_key_to_pos.find(k))
            return optional<unsigned>(p->first);
        else
            return optional<unsigned>();
    }

    // useful if \c CMP only compares part of \c K
    K const * get_key(K const & k) const {
        if (auto p = m_key_to_pos.find(k))
            return m_pos_to_key.find(*p);
        else
            return nullptr;
    }

    void clear() {
        m_key_to_pos.clear();
        m_pos_to_key.clear();
        m_next = 0;
    }

    void insert(K const & k, unsigned prio = 0) {
        if (m_next == std::numeric_limits<unsigned>::max())
            normalize();
        if (auto pos = m_key_to_pos.find(k)) {
            m_pos_to_key.erase(*pos);
        }
        m_key_to_pos.insert(k, pos(prio, m_next));
        m_pos_to_key.insert(pos(prio, m_next), k);
        m_next++;
    }

    void erase(K const & k) {
        if (auto pos = m_key_to_pos.find(k)) {
            m_pos_to_key.erase(*pos);
            m_key_to_pos.erase(k);
        }
    }
};
}
