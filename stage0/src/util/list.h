/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <iterator>
#include "runtime/debug.h"
#include "runtime/optional.h"
#include "runtime/buffer.h"
#include "util/rc.h"

namespace lean {
/**
   \brief Basic list template.
*/
template<typename T>
class list {
public:
    class cell {
        MK_LEAN_RC()
        T      m_head;
        list   m_tail;
        template<typename... Fields>
        cell(bool, list const & t, Fields&&... head):m_rc(1), m_head(head...), m_tail(t) {}
    public:
        cell(T const & h, list const & t):m_rc(1), m_head(h), m_tail(t) {}
        ~cell() {}
        T const & head() const { return m_head; }
        list const & tail() const { return m_tail; }
        void dealloc();
    };
private:
    cell * m_ptr;
    cell * steal_ptr() { cell * r = m_ptr; m_ptr = nullptr; return r; }
public:
    list():m_ptr(nullptr) {}
    list(T const & h, list const & t):m_ptr(new cell(h, t)) {}
    explicit list(T const & h):m_ptr(new cell(h, list())) {}
    list(list const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    list(list&& s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    list(std::initializer_list<T> const & l):list() {
        auto it = l.end();
        while (it != l.begin()) {
            --it;
            *this = list(*it, *this);
        }
    }
    explicit list(cell * c):m_ptr(c) { if (m_ptr) m_ptr->inc_ref(); }
    ~list() {
        if (m_ptr && m_ptr->dec_ref_core()) {
            cell * it = m_ptr;
            while (true) {
                lean_assert(it);
                lean_assert(it->get_rc() == 0);
                cell * next = it->m_tail.steal_ptr();
                it->dealloc();
                if (next && next->dec_ref_core()) {
                    it = next;
                } else {
                    break;
                }
            }
        }
    }

    list & operator=(list const & s) { LEAN_COPY_REF(s); }
    list & operator=(list && s) { LEAN_MOVE_REF(s); }

    /**
        \brief Return internal representation.
        This method is useful when we know the list is not going to be deleted and
        we want to save a temporary reference to it. Use raw() prevents us from updating the
        reference counters.

        \warning Use it with care. The main risk of storing references to cell is that
        the list may be deleted.
    */
    cell * raw() const { return m_ptr; }

    /** \brief Return true iff it is not the empty/nil list. */
    explicit operator bool() const { return m_ptr != nullptr; }

    friend bool is_nil(list const & l) { return l.m_ptr == nullptr; }
    friend bool empty(list const & l) { return is_nil(l); }
    friend T const & head(list const & l) { lean_assert(!is_nil(l)); return l.m_ptr->m_head; }
    friend list const & tail(list const & l) { lean_assert(!is_nil(l)); return l.m_ptr->m_tail; }

    /** \brief Pointer equality. Return true iff \c l1 and \c l2 point to the same memory location. */
    friend bool is_eqp(list const & l1, list const & l2) { return l1.m_ptr == l2.m_ptr; }
    friend bool is_eqp(list const & l1, cell const * l2) { return l1.m_ptr == l2; }

    /** \brief Return true iff l_2 is of the form [a_1, ..., a_n, l_1] for n >= 0 */
    friend bool is_suffix_eqp(list const & l_1, list const & l_2) {
        list const * it = &l_2;
        while (!empty(*it)) {
            if (is_eqp(*it, l_1))
                return true;
            it = &tail(*it);
        }
        return is_eqp(*it, l_1);
    }

    template<typename... Args>
    void emplace_front(Args&&... args) {
        cell * new_ptr = new cell(true, *this, args...);
        if (m_ptr) m_ptr->dec_ref();
        m_ptr = new_ptr;
    }

    /** \brief Structural equality. */
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

template<typename T>
void list<T>::cell::dealloc() {
    delete this;
}

template<typename T> inline list<T>         cons(T const & h, list<T> const & t) { return list<T>(h, t); }
template<typename T> inline T const &       car(list<T> const & l) { return head(l); }
template<typename T> inline list<T> const & cdr(list<T> const & l) { return tail(l); }
template<typename T> inline optional<T>     head_opt(list<T> const & l) { return l ? some(head(l)) : optional<T>(); }
template<typename T> inline list<T>         to_list(T const & v) { return list<T>(v); }
template<typename T> inline list<T>         to_list(optional<T> const & v) { return v ? to_list(*v) : list<T>(); }
template<typename T> inline list<T>         to_list(T const * v) { return v ? to_list(*v) : list<T>(); }
template<typename T> inline list<T>         ptr_to_list(list<T> const * l) { return l ? *l : list<T>(); }

template<typename T, typename CMP>
int cmp(list<T> const & l1, list<T> const & l2, CMP const & c) {
    list<T> const * it1 = &l1;
    list<T> const * it2 = &l2;
    while (*it1 && *it2) {
        int r = c(head(*it1), head(*it2));
        if (r != 0) return r;
        it1 = &tail(*it1);
        it2 = &tail(*it2);
    }
    if (!*it1) {
        return !*it2 ? 0 : -1;
    } else {
        lean_assert(*it1 && !*it2);
        return 1;
    }
}

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
template<typename It> list<typename std::iterator_traits<It>::value_type>
to_list(It const & begin, It const & end,
        list<typename std::iterator_traits<It>::value_type> const & ls = list<typename std::iterator_traits<It>::value_type>()) {
    list<typename std::iterator_traits<It>::value_type> r = ls;
    auto it = end;
    while (it != begin) {
        --it;
        r = cons(*it, r);
    }
    return r;
}

template<typename T>
list<T> to_list(buffer<T> const & b) {
    return to_list(b.begin(), b.end());
}

/** \brief Return <tt>reverse(to_list(begin, end))</tt> */
template<typename It> list<typename std::iterator_traits<It>::value_type> reverse_to_list(It const & begin, It const & end) {
    list<typename std::iterator_traits<It>::value_type> r;
    for (auto it = begin; it != end; ++it)
        r = cons(*it, r);
    return r;
}

template<typename T>
list<T> reverse_to_list(buffer<T> const & b) {
    return reverse_to_list(b.begin(), b.end());
}
}
