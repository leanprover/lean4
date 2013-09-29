/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rc.h"
#include "util/debug.h"

namespace lean {
/**
   \brief ML-like lazy lists.
*/
template<typename T>
class lazy_list {
public:
    class cell {
        MK_LEAN_RC();
        void dealloc() { delete this; }
        T      m_head;
    public:
        cell(T const & h):m_rc(0), m_head(h) {}
        virtual ~cell() {}
        T const & head() const { return m_head; }
        virtual lazy_list tail() const { return lazy_list(); }
    };

private:
    class explicit_cell : public cell {
        lazy_list m_tail;
    public:
        explicit_cell(T const & h, lazy_list const & l):cell(h), m_tail(l) {}
        virtual ~explicit_cell() {}
        virtual lazy_list tail() const { return m_tail; }
    };

    template<typename Tail>
    class lazy_cell : public cell {
        Tail m_tail;
    public:
        lazy_cell(T const & h, Tail const & t):cell(h), m_tail(t) {}
        virtual ~lazy_cell() {}
        virtual lazy_list tail() const { return m_tail(); }
    };

    cell * m_ptr;
public:
    lazy_list():m_ptr(nullptr) {}
    lazy_list(T const & h):m_ptr(new cell(h)) { m_ptr->inc_ref(); }
    lazy_list(T const & h, lazy_list const & t):m_ptr(new explicit_cell(h, t)) { m_ptr->inc_ref(); }
    template<typename F>
    lazy_list(T const & h, F const & f):m_ptr(new lazy_cell<F>(h, f)) { m_ptr->inc_ref(); }
    lazy_list(lazy_list const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    lazy_list(lazy_list&& s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~lazy_list() { if (m_ptr) m_ptr->dec_ref(); }

    lazy_list & operator=(lazy_list const & s) { LEAN_COPY_REF(list, s); }
    lazy_list & operator=(lazy_list && s) { LEAN_MOVE_REF(list, s); }

    operator bool() const { return m_ptr != nullptr; }

    friend T const & head(lazy_list const & l) { lean_assert(l); return l.m_ptr->head(); }
    friend lazy_list tail(lazy_list const & l) { lean_assert(l); return l.m_ptr->tail(); }
    friend lazy_list cons(T const & h, lazy_list const & t) { return lazy_list(h, t); }

    class iterator {
        friend class lazy_list;
        lazy_list m_it;
        iterator(lazy_list const & it):m_it(it) {}
    public:
        iterator(iterator const & s):m_it(s.m_it) {}
        iterator & operator++() { m_it = tail(m_it); return *this; }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() { lean_assert(m_it); return head(m_it); }
        T const * operator->() { lean_assert(m_it); return &(head(m_it)); }
    };

    iterator begin() const { return iterator(*this); }
    iterator end() const { return iterator(lazy_list()); }
};
}
