/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "rc.h"
#include "debug.h"

namespace lean {
/**
   \brief Basic list template.

   Remark: == is pointer equality.
*/
template<typename T>
class list {
    struct cell {
        MK_LEAN_RC()
        T      m_head;
        list   m_tail;
        cell(T const & h, list const & t):m_rc(1), m_head(h), m_tail(t) {}
        ~cell() {}
        void dealloc() { delete this; }
    };
    cell * m_ptr;
public:
    list():m_ptr(nullptr) {}
    list(T const & h, list const & t):m_ptr(new cell(h, t)) {}
    list(list const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    list(list&& s):m_ptr(s.m_ptr) { s.m_ptr = 0; }
    ~list() { if (m_ptr) m_ptr->dec_ref(); }

    list & operator=(list const & s) { LEAN_COPY_REF(list, s); }
    list & operator=(list && s) { LEAN_MOVE_REF(list, s); }

    friend bool is_nil(list const & l) { return l.m_ptr == nullptr; }
    friend T const & head(list const & l) { lean_assert(!is_nil(l)); return l.m_ptr->m_head; }
    friend list const & tail(list const & l) { lean_assert(!is_nil(l)); return l.m_ptr->m_tail; }
    friend bool operator==(list const & l1, list const & l2) { return l1.m_ptr == l2.m_ptr; }
    friend bool operator!=(list const & l1, list const & l2) { return l1.m_ptr != l2.m_ptr; }
};

template<typename T> inline list<T>         cons(T const & h, list<T> const & t) { return list<T>(h, t); }
template<typename T> inline T const &       car(list<T> const & l) { return head(l); }
template<typename T> inline list<T> const & cdr(list<T> const & l) { return tail(l); }

template<typename T> inline std::ostream & operator<<(std::ostream & out, list<T> const & l) {
    out << "(";
    bool first = true;
    list<T> const * ptr = &l;
    while (!is_nil(*ptr)) {
        if (first)
            first = false;
        else
            out << " ";
        out << head(*ptr);
        ptr = &tail(*ptr);
    }
    out << ")";
    return out;
}
}
