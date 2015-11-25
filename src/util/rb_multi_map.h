/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "util/rb_map.h"
#include "util/list_fn.h"

namespace lean {

template<typename T, typename V, typename Cmp>
class rb_multi_map {
    rb_map<T, list<V>, Cmp> m_map;

public:
    rb_multi_map() {}
    bool empty() const { return m_map.empty(); }
    bool contains(T const & t) const { return m_map.contains(t); }
    list<V> const * find(T const & t) const { return m_map.find(t); }
    void erase(T const & t) { m_map.erase(t); }
    template<typename P> void filter(T const & t, P && p) {
        if (auto it = m_map.find(t)) {
            auto new_vs = ::lean::filter(*it, std::forward<P>(p));
            if (!new_vs)
                m_map.erase(t);
            else
                m_map.insert(t, new_vs);
        }
    }
    void erase(T const & t, V const & v) {
        filter(t, [&](V const & v2) { return v != v2; });
    }
    void insert(T const & t, V const & v) {
        if (auto it = m_map.find(t))
            m_map.insert(t, cons(v, ::lean::filter(*it, [&](V const & v2) { return v != v2; })));
        else
            m_map.insert(t, to_list(v));
    }
    template<typename F> void for_each(F && f) const { m_map.for_each(f); }
    template<typename F> void for_each_entry(F && f) const {
        m_map.for_each([&](T const & t, list<V> const & vs) {
                for (V const & v : vs)
                    f(t, v);
            });
    }
};
}
