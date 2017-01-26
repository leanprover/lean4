/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/pair.h"
#include "util/rb_tree.h"

namespace lean {
/**
   \brief Wrapper for implementing maps using red black trees.
*/
template<typename K, typename T, typename CMP>
class rb_map {
public:
    typedef pair<K, T> entry;
private:
    struct entry_cmp : private CMP {
        entry_cmp(CMP const & c):CMP(c) {}
        int operator()(entry const & e1, entry const & e2) const { return CMP::operator()(e1.first, e2.first); }
        CMP const & get_cmp() const { return *this; }
    };
    rb_tree<entry, entry_cmp> m_map;
public:
    rb_map(CMP const & cmp = CMP()):m_map(entry_cmp(cmp)) {}
    friend void swap(rb_map & a, rb_map & b) { swap(a.m_map, b.m_map); }
    bool empty() const { return m_map.empty(); }
    void clear() { m_map.clear(); }
    friend bool is_eqp(rb_map const & m1, rb_map const & m2) { return is_eqp(m1.m_map, m2.m_map); }
    unsigned size() const { return m_map.size(); }
    void insert(K const & k, T const & v) { m_map.insert(mk_pair(k, v)); }
    T const * find(K const & k) const { auto e = m_map.find(mk_pair(k, T())); return e ? &(e->second) : nullptr; }
    bool contains(K const & k) const { return m_map.contains(mk_pair(k, T())); }
    void erase(K const & k) { m_map.erase(mk_pair(k, T())); }

    unsigned get_rc() const { return m_map.get_rc(); }

    CMP const & get_cmp() const { return m_map.get_cmp().get_cmp(); }

    T erase_min() {
        lean_assert(!empty());
        T r = m_map.min()->second;
        m_map.erase_min();
        return r;
    }

    T min() const { lean_assert(!empty()); return m_map.min()->second; }
    T max() const { lean_assert(!empty()); return m_map.max()->second; }

    class ref {
        rb_map & m_map;
        K const &   m_key;
    public:
        ref(rb_map & m, K const & k):m_map(m), m_key(k) {}
        ref & operator=(T const & v) { m_map.insert(m_key, v); return *this; }
        operator T const &() const {
            T const * e = m_map.find(m_key);
            if (e) {
                return *e;
            } else {
                m_map.insert(m_key, T());
                return *(m_map.find(m_key));
            }
        }
    };

    /**
       \brief Returns a reference to the value that is mapped to a key equivalent to key,
       performing an insertion if such key does not already exist.
    */
    ref operator[](K const & k) { return ref(*this, k); }

    template<typename F>
    void for_each(F && f) const {
        auto f_prime = [&](entry const & e) { f(e.first, e.second); };
        return m_map.for_each(f_prime);
    }

    template<typename F>
    optional<T> find_if(F && f) const {
        auto f_prime = [&](entry const & e) { return f(e.first, e.second); };
        if (auto r = m_map.find_if(f_prime))
            return optional<T>(r->second);
        else
            return optional<T>();
    }

    /* Similar to find_if but searches keys backwards (from greatest to least) */
    template<typename F>
    optional<T> back_find_if(F && f) const {
        auto f_prime = [&](entry const & e) { return f(e.first, e.second); };
        if (auto r = m_map.back_find_if(f_prime))
            return optional<T>(r->second);
        else
            return optional<T>();
    }

    template<typename F>
    void for_each_greater(K const & k, F && f) const {
        auto f_prime = [&](entry const & e) { f(e.first, e.second); };
        m_map.for_each_greater(mk_pair(k, T()), f_prime);
    }

    /** \brief (For debugging) Display the content of this splay map. */
    friend std::ostream & operator<<(std::ostream & out, rb_map const & m) {
        out << "{";
        m.for_each([&out](K const & k, T const & v) {
                out << k << " |-> " << v << "; ";
            });
        out << "}";
        return out;
    }

    bool equal_keys(rb_map const & other) const {
        return m_map.equal_elems(other.m_map);
    }

    // For debugging purposes
    void display(std::ostream & out) const { m_map.display(out); }

    class iterator : public rb_tree<entry, entry_cmp>::iterator {
    public:
        iterator(rb_map const & map):rb_tree<entry, entry_cmp>::iterator(map.m_map) {}
    };
};
template<typename K, typename T, typename CMP>
rb_map<K, T, CMP> insert(rb_map<K, T, CMP> const & m, K const & k, T const & v) {
    auto r = m;
    r.insert(k, v);
    return r;
}
template<typename K, typename T, typename CMP>
rb_map<K, T, CMP> erase(rb_map<K, T, CMP> const & m, K const & k) {
    auto r = m;
    r.erase(k);
    return r;
}
template<typename K, typename T, typename CMP, typename F>
void for_each(rb_map<K, T, CMP> const & m, F && f) {
    return m.for_each(f);
}

template<typename T> using unsigned_map = rb_map<unsigned, T, unsigned_cmp>;
}
