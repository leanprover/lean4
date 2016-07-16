/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "util/list.h"
#include "kernel/expr.h"
#include "library/io_state_stream.h"

namespace lean {
struct head_index {
    expr_kind m_kind;
    name      m_name;
    explicit head_index(expr_kind k = expr_kind::Var):m_kind(k) {}
    explicit head_index(name const & c):m_kind(expr_kind::Constant), m_name(c) {}
    head_index(expr const & e);
    expr_kind kind() const { return m_kind; }
    name const & get_name() const { return m_name; }

    struct cmp {
        int operator()(head_index const & i1, head_index const & i2) const;
    };

    friend std::ostream & operator<<(std::ostream & out, head_index const & head_idx);
};

io_state_stream const & operator<<(io_state_stream const & out, head_index const & head_idx);

/**
    \brief Very simple indexing data-structure that allow us to map the head symbol of an expression to
    a list of values.

    The index is the expression kind and a name (if it is a constant).

    This index is very naive, but it is effective for many applications. */
template<typename V, typename GetPrio>
class head_map_prio : private GetPrio {
    rb_map<head_index, list<V>, head_index::cmp> m_map;

    unsigned get_priority(V const & v) const { return GetPrio::operator()(v); }

    list<V> insert_prio(V const & v, list<V> const & vs) {
        if (!vs)
            return to_list(v);
        else if (get_priority(v) >= get_priority(head(vs)))
            return cons(v, vs);
        else
            return cons(head(vs), insert_prio(v, tail(vs)));
    }

public:
    head_map_prio() {}
    head_map_prio(GetPrio const & g):GetPrio(g) {}
    void clear() { m_map = rb_map<head_index, list<V>, head_index::cmp>(); }
    bool empty() const { return m_map.empty(); }
    bool contains(head_index const & h) const { return m_map.contains(h); }
    list<V> const * find(head_index const & h) const { return m_map.find(h); }
    void erase(head_index const & h) { m_map.erase(h); }
    template<typename P> void filter(head_index const & h, P && p) {
        if (auto it = m_map.find(h)) {
            auto new_vs = ::lean::filter(*it, std::forward<P>(p));
            if (!new_vs)
                m_map.erase(h);
            else
                m_map.insert(h, new_vs);
        }
    }
    void erase(head_index const & h, V const & v) {
        return filter(h, [&](V const & v2) { return v != v2; });
    }
    void insert(head_index const & h, V const & v) {
        if (auto it = m_map.find(h))
            m_map.insert(h, insert_prio(v, ::lean::filter(*it, [&](V const & v2) { return v != v2; })));
        else
            m_map.insert(h, to_list(v));
    }
    template<typename F> void for_each(F && f) const { m_map.for_each(f); }
    template<typename F> void for_each_entry(F && f) const {
        m_map.for_each([&](head_index const & h, list<V> const & vs) {
                for (V const & v : vs)
                    f(h, v);
            });
    }
};

template<typename V>
struct constant_priority_fn { unsigned operator()(V const &) const { return 0; } };

template<typename V>
class head_map : public head_map_prio<V, constant_priority_fn<V>> {
public:
    head_map() {}
};
}
