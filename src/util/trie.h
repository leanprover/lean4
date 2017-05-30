/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <string>
#include "util/rb_map.h"
#include "util/optional.h"
#include "util/buffer.h"

namespace lean {
template<typename Key, typename Val, typename KeyCMP>
class trie : public KeyCMP {
    friend struct cell;

    struct cell {
        rb_map<Key, trie, KeyCMP> m_children;
        optional<Val>             m_value;
        MK_LEAN_RC();
        void dealloc() { delete this; }
        cell():m_rc(0) {}
        cell(Val const & v):m_value(v), m_rc(0) {}
        cell(cell const & s):m_children(s.m_children), m_value(s.m_value), m_rc(0) {}
    };

    static trie ensure_unshared(trie && n) {
        if (n.is_shared())
            return trie(new cell(*n.m_ptr));
        else
            return n;
    }

    template<typename It>
    static trie insert(trie && n, It const & begin, It const & end, Val const & v) {
        trie h = ensure_unshared(n.steal());
        if (!h.m_ptr)
            h = trie(new cell());
        if (begin == end) {
            h->m_value = v;
            return h;
        } else {
            Key k = *begin;
            trie const * c = h->m_children.find(k);
            It it(begin); it++;
            if (c == nullptr) {
                h->m_children.insert(k, insert(trie(), it, end, v));
            } else {
                trie n(*c);
                h->m_children.erase(k);
                h->m_children.insert(k, insert(n.steal(), it, end, v));
            }
            return h;
        }
    }

    static trie merge(trie && t1, trie const & t2) {
        trie new_t1     = ensure_unshared(t1.steal());
        new_t1->m_value = t2->m_value;
        t2->m_children.for_each([&](Key const & k, trie const & c2) {
                trie const * c1 = new_t1->m_children.find(k);
                if (c1 == nullptr) {
                    new_t1->m_children.insert(k, c2);
                } else {
                    trie n1(*c1);
                    new_t1->m_children.erase(k);
                    new_t1->m_children.insert(k, trie::merge(n1.steal(), c2));
                }
            });
        return new_t1;
    }

    template<typename F>
    static void for_each(F && f, trie const & n, buffer<Key> & prefix) {
        if (n->m_value) {
            f(prefix.size(), prefix.data(), *(n->m_value));
        }
        n->m_children.for_each([&](Key const & k, trie const & c) {
                prefix.push_back(k);
                trie::for_each(f, c, prefix);
                prefix.pop_back();
            });
    }

    cell * m_ptr;
    cell * operator->() const { lean_assert(m_ptr); return m_ptr; }

    trie(cell * ptr):m_ptr(ptr) { if (m_ptr) ptr->inc_ref(); }
    trie steal() { trie r; swap(r, *this); return r; }
public:
    trie():m_ptr(nullptr) {}
    trie(trie const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    trie(trie && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~trie() { if (m_ptr) m_ptr->dec_ref(); }

    trie & operator=(trie const & n) { LEAN_COPY_REF(n); }
    trie & operator=(trie&& n) { LEAN_MOVE_REF(n); }
    bool is_shared() const { return m_ptr && m_ptr->get_rc() > 1; }
    friend void swap(trie & n1, trie & n2) { std::swap(n1.m_ptr, n2.m_ptr); }

    template<typename It>
    Val const * find(It const & begin, It const & end) const {
        if (!m_ptr)
            return nullptr;
        cell const * c = m_ptr;
        for (It it = begin; it != end; ++it) {
            trie const * n = c->m_children.find(*it);
            if (!n)
                return nullptr;
            c = n->m_ptr;
        }
        if (c->m_value)
            return &c->m_value.value();
        else
            return nullptr;
    }

    template<typename It>
    void insert(It const & begin, It const & end, Val const & v) {
        *this = insert(steal(), begin, end, v);
    }

    trie const * find(Key const & k) const {
        return m_ptr ? m_ptr->m_children.find(k) : nullptr;
    }

    Val const * value() const {
        if (m_ptr && m_ptr->m_value)
            return &m_ptr->m_value.value();
        else
            return nullptr;
    }

    void merge(trie const & t) {
        *this = merge(steal(), t);
    }

    template<typename F>
    void for_each(F && f) const {
        if (m_ptr) {
            buffer<Key> prefix;
            for_each(f, *this, prefix);
        }
    }

    // for debugging purposes
    void display(std::ostream & out) const {
        for_each([&](unsigned num_keys, Key const * keys, Val const & v) {
                for (unsigned i = 0; i < num_keys; i++) {
                    if (i > 0) out << ", ";
                    out << keys[i];
                }
                out << " -> " << v << "\n";
            });
    }
};

struct char_cmp { int operator()(char c1, char c2) const { return c1 < c2 ? -1 : (c1 == c2 ? 0 : 1); } };

template<typename Val>
using ctrie = trie<char, Val, char_cmp>;

template<typename Val>
inline ctrie<Val> insert(ctrie<Val> const & t, std::string const & str, Val const & v) {
    ctrie<Val> r(t);
    r.insert(str.begin(), str.end(), v);
    return r;
}

template<typename Val>
inline ctrie<Val> insert(ctrie<Val> const & t, char const * str, Val const & v) {
    ctrie<Val> r(t);
    r.insert(str, str+strlen(str), v);
    return r;
}

template<typename Val>
Val const * find(ctrie<Val> const & t, std::string const & str) { return t.find(str.begin(), str.end()); }

template<typename Val>
Val const * find(ctrie<Val> const & t, char const * str) { return t.find(str, str + strlen(str)); }

template<typename Val>
inline ctrie<Val> merge(ctrie<Val> const & t1, ctrie<Val> const & t2) {
    ctrie<Val> r(t1);
    r.merge(t2);
    return r;
}
}
