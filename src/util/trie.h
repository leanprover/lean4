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
    struct cell;
    struct node {
        cell * m_ptr;
        node():m_ptr(new cell()) { m_ptr->inc_ref(); }
        node(cell * ptr):m_ptr(ptr) { if (m_ptr) ptr->inc_ref(); }
        node(node const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
        node(node && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
        ~node() { if (m_ptr) m_ptr->dec_ref(); }
        node & operator=(node const & n) { LEAN_COPY_REF(n); }
        node & operator=(node&& n) { LEAN_MOVE_REF(n); }
        cell * operator->() const { lean_assert(m_ptr); return m_ptr; }
        bool is_shared() const { return m_ptr && m_ptr->get_rc() > 1; }
        friend void swap(node & n1, node & n2) { std::swap(n1.m_ptr, n2.m_ptr); }
        node steal() { node r; swap(r, *this); return r; }
    };

    struct cell {
        rb_map<Key, node, KeyCMP> m_children;
        optional<Val>             m_value;
        MK_LEAN_RC();
        void dealloc() { delete this; }
        cell():m_rc(0) {}
        cell(Val const & v):m_value(v), m_rc(0) {}
        cell(cell const & s):m_children(s.m_children), m_value(s.m_value), m_rc(0) {}
    };

    static node ensure_unshared(node && n) {
        if (n.is_shared())
            return node(new cell(*n.m_ptr));
        else
            return n;
    }

    template<typename It>
    static node insert(node && n, It const & begin, It const & end, Val const & v) {
        node h = ensure_unshared(n.steal());
        if (begin == end) {
            h->m_value = v;
            return h;
        } else {
            Key k = *begin;
            node const * c = h->m_children.find(k);
            It it(begin); it++;
            if (c == nullptr) {
                h->m_children.insert(k, insert(node(), it, end, v));
            } else {
                node n(*c);
                h->m_children.erase(k);
                h->m_children.insert(k, insert(n.steal(), it, end, v));
            }
            return h;
        }
    }

    static node merge(node && t1, node const & t2) {
        node new_t1    = ensure_unshared(t1.steal());
        new_t1->m_value = t2->m_value;
        t2->m_children.for_each([&](Key const & k, node const & c2) {
                node const * c1 = new_t1->m_children.find(k);
                if (c1 == nullptr) {
                    new_t1->m_children.insert(k, c2);
                } else {
                    node n1(*c1);
                    new_t1->m_children.erase(k);
                    new_t1->m_children.insert(k, merge(n1.steal(), c2));
                }
            });
        return new_t1;
    }

    template<typename F>
    static void for_each(F && f, node const & n, buffer<Key> & prefix) {
        if (n->m_value) {
            f(prefix.size(), prefix.data(), *(n->m_value));
        }
        n->m_children.for_each([&](Key const & k, node const & c) {
                prefix.push_back(k);
                for_each(f, c, prefix);
                prefix.pop_back();
            });
    }

    node m_root;
    trie(node const & n):m_root(n) {}
public:
    trie() {}
    trie(trie const & s):m_root(s.m_root) {}
    trie(trie && s):m_root(s.m_root) {}

    trie & operator=(trie const & s) { m_root = s.m_root; return *this; }
    trie & operator=(trie && s) { m_root = s.m_root; return *this; }

    template<typename It>
    optional<Val> find(It const & begin, It const & end) const {
        node const * n = &m_root;
        for (It it = begin; it != end; ++it) {
            n = (*n)->m_children.find(*it);
            if (!n)
                return optional<Val>();
        }
        return (*n)->m_value;
    }

    template<typename It>
    void insert(It const & begin, It const & end, Val const & v) {
        m_root = insert(m_root.steal(), begin, end, v);
    }

    optional<trie> find(Key const & k) const {
        node const * c = m_root->m_children.find(k);
        if (c)
            return optional<trie>(trie(*c));
        else
            return optional<trie>();
    }

    void merge(trie const & t) {
        m_root = merge(m_root.steal(), t.m_root);
    }

    template<typename F>
    void for_each(F && f) const {
        buffer<Key> prefix;
        for_each(f, m_root, prefix);
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
optional<Val> find(ctrie<Val> const & t, std::string const & str) { return t.find(str.begin(), str.end()); }

template<typename Val>
optional<Val> find(ctrie<Val> const & t, char const * str) { return t.find(str, str + strlen(str)); }

template<typename Val>
inline ctrie<Val> merge(ctrie<Val> const & t1, ctrie<Val> const & t2) {
    ctrie<Val> r(t1);
    r.merge(t2);
    return r;
}
}
