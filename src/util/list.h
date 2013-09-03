/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <iterator>
#include "rc.h"
#include "debug.h"

namespace lean {
/**
   \brief Basic list template.
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
    list(T const & h):m_ptr(new cell(h, list())) {}
    list(list const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    list(list&& s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    list(std::initializer_list<T> const & l):list() {
        auto it = l.end();
        while (it != l.begin()) {
            --it;
            *this = list(*it, *this);
        }
    }
    ~list() { if (m_ptr) m_ptr->dec_ref(); }

    list & operator=(list const & s) { LEAN_COPY_REF(list, s); }
    list & operator=(list && s) { LEAN_MOVE_REF(list, s); }

    operator bool() const { return m_ptr != nullptr; }

    friend bool is_nil(list const & l) { return l.m_ptr == nullptr; }
    friend T const & head(list const & l) { lean_assert(!is_nil(l)); return l.m_ptr->m_head; }
    friend list const & tail(list const & l) { lean_assert(!is_nil(l)); return l.m_ptr->m_tail; }

    friend bool is_eqp(list const & l1, list const & l2) { return l1.m_ptr == l2.m_ptr; }
    friend bool operator==(list const & l1, list const & l2) {
        cell * it1 = l1.m_ptr;
        cell * it2 = l2.m_ptr;
        while (it1 != nullptr && it2 != nullptr) {
            if (it1 == it2)
                return true;
            if (it1->m_head != it2->m_head)
                return false;
            it1 = it1->m_tail.m_ptr;
            it2 = it2->m_tail.m_ptr;
        }
        return it1 == nullptr && it2 == nullptr;
    }
    friend bool operator!=(list const & l1, list const & l2) { return !(l1 == l2); }

    /** \brief List iterator object. */
    class iterator {
        friend class list;
        cell const * m_it;
        iterator(cell const * it):m_it(it) {}
    public:
        typedef std::forward_iterator_tag iterator_category;
        typedef T         value_type;
        typedef unsigned  difference_type;
        typedef T const * pointer;
        typedef T const & reference;

        iterator(iterator const & s):m_it(s.m_it) {}
        iterator & operator++() { m_it = m_it->m_tail.m_ptr; return *this; }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() { lean_assert(m_it); return m_it->m_head; }
        T const * operator->() { lean_assert(m_it); return &(m_it->m_head); }
    };

    iterator begin() const { return iterator(m_ptr); }
    iterator end() const { return iterator(nullptr); }
};

template<typename T> inline list<T>         cons(T const & h, list<T> const & t) { return list<T>(h, t); }
template<typename T> inline T const &       car(list<T> const & l) { return head(l); }
template<typename T> inline list<T> const & cdr(list<T> const & l) { return tail(l); }

template<typename T> inline std::ostream & operator<<(std::ostream & out, list<T> const & l) {
    out << "(";
    bool first = true;
    list<T> const * ptr = &l;
    while (*ptr) {
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

template<typename T> unsigned length(list<T> const & l) {
    unsigned r = 0;
    list<T> const * it = &l;
    while (*it) {
        r++;
        it = &tail(*it);
    }
    return r;
}

/** \brief Return a list containing the elements in the subrange <tt>[begin, end)</tt>. */
template<typename It, typename T = typename It::value_type> list<T> copy_to_list(It const & begin, It const & end) {
    list<T> r;
    auto it = end;
    while (it != begin) {
        --it;
        r = cons(*it, r);
    }
    return r;
}
}
