/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/debug.h"
#include "util/rc.h"
#include "util/optional.h"
#include "util/pair.h"

namespace lean {
/**
   \brief ML-like lazy lists.
*/
template<typename T>
class lazy_list {
public:
    typedef optional<pair<T, lazy_list>> maybe_pair; // head and tail pair
private:
    class cell_base {
        MK_LEAN_RC();
        void dealloc() { delete this; }
    public:
        cell_base():m_rc(0) {}
        virtual ~cell_base() {}
        virtual maybe_pair pull() const = 0;
    };

    template<typename F>
    class cell : public cell_base {
        F m_f;
    public:
        cell(F && f):cell_base(), m_f(f) {}
        virtual ~cell() {}
        virtual maybe_pair pull() const { return m_f(); }
    };

    class cell_singleton : public cell_base {
        T m_val;
    public:
        cell_singleton(T const & v):cell_base(), m_val(v) {}
        cell_singleton(T && v):cell_base(), m_val(std::move(v)) {}
        virtual ~cell_singleton() {}
        virtual maybe_pair pull() const {
            lazy_list empty;
            return maybe_pair(m_val, empty);
        }
    };

    class cell_pair : public cell_base {
        T         m_head;
        lazy_list m_tail;
    public:
        cell_pair(T const & h, lazy_list const & t):cell_base(), m_head(h), m_tail(t) {}
        virtual ~cell_pair() {}
        virtual maybe_pair pull() const {
            return maybe_pair(m_head, m_tail);
        }
    };

    cell_base * m_ptr;
public:
    lazy_list():m_ptr(nullptr) {}
    lazy_list(lazy_list const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    lazy_list(lazy_list && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    lazy_list(T const & v):m_ptr(new cell_singleton(v)) { m_ptr->inc_ref(); }
    lazy_list(T && v):m_ptr(new cell_singleton(std::forward<T>(v))) { m_ptr->inc_ref(); }
    lazy_list(T const & h, lazy_list const & t):m_ptr(new cell_pair(h, t)) { m_ptr->inc_ref(); }
    ~lazy_list() { if (m_ptr) m_ptr->dec_ref(); }

    lazy_list & operator=(lazy_list const & s) { LEAN_COPY_REF(s); }
    lazy_list & operator=(lazy_list && s) { LEAN_MOVE_REF(s); }

    /**
        \brief Return true if the lazy_list is definitely empty. This is an approximated test (i.e., it is not an "iff").
        Here are examples where this method will return true.

        1) lazy_list empty;
           lean_assert(is_nil(empty));

        2) lazy_list singleton(v);
           maybe_pair p = singleton.pull();
           lean_assert(p);
           lean_assert(is_nil(p->second));

        3) assume is_nil(l), then
           lazy_list singleton(v, l);
           maybe_pair p = singleton.pull();
           lean_assert(p);
           lean_assert(is_nil(p->second));
    */
    bool is_nil() const { return m_ptr == nullptr; }

    maybe_pair pull() const {
        if (m_ptr)
            return m_ptr->pull();
        else
            return maybe_pair();
    }

    friend T head(lazy_list const & l) { return l.pull()->first; }
    friend lazy_list tail(lazy_list const & l) { return l.pull()->second; }

    template<typename F>
    static lazy_list mk_lazy_list_core(F && f) {
        lazy_list r;
        r.m_ptr = new cell<F>(std::forward<F>(f));
        r.m_ptr->inc_ref();
        return r;
    }
};
template<typename T, typename F>
lazy_list<T> mk_lazy_list(F && f) {
    return lazy_list<T>::mk_lazy_list_core(std::forward<F>(f));
}
}
