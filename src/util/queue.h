/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "list_fn.h"

namespace lean {
/**
   \brief Functional queue
*/
template<typename T>
class queue {
    list<T> m_front;
    list<T> m_rear;
    queue(list<T> const & f, list<T> const & r):m_front(f), m_rear(r) {}
public:
    queue() {}
    queue(unsigned num, T const * as) { m_front = to_list(as, as + num); }
    queue(std::initializer_list<T> const & l):queue(l.size(), l.begin()) {}

    /** \brief Return true iff the list is empty (complexity O(1)) */
    bool is_empty() const { return is_nil(m_front) && is_nil(m_rear); }

    /** \brief Return the size of the queue (complexity O(n)) */
    unsigned size() const { return length(m_front) + length(m_rear); }

    /** \brief Return the queue <tt>(v :: q)</tt> (complexity O(1)) */
    friend queue push_front(queue<T> const & q, T const & v) { return queue(cons(v, q.m_front), q.m_rear); }

    /** \brief Return the queue <tt>(q :: v)</tt> (complexity O(1)) */
    friend queue push_back(queue<T> const & q, T const & v) { return queue(q.m_front, cons(v, q.m_rear)); }

    /**
        \brief Return the pair <tt>(q, v)</tt> for a queue <tt>(v :: q)</tt>.
        Complexity: worst case is O(n), average O(1)

        \pre !is_empty(q)
    */
    friend std::pair<queue<T>, T> pop_front(queue<T> const & q) {
        lean_assert(!q.is_empty());
        if (is_nil(q.m_front)) {
            if (is_nil(cdr(q.m_rear))) {
                return mk_pair(queue(), car(q.m_rear));
            } else {
                auto p = split_reverse_second(q.m_rear);
                return mk_pair(queue(cdr(p.second), p.first), car(p.second));
            }
        } else {
            return mk_pair(queue(cdr(q.m_front), q.m_rear), car(q.m_front));
        }
    }

    /**
        \brief Return the pair <tt>(q, v)</tt> for a queue <tt>(q :: v)</tt>.
        Complexity: worst case is O(n), average O(1)

        \pre !is_empty(q)
    */
    friend std::pair<queue<T>, T> pop_back(queue<T> const & q) {
        lean_assert(!q.is_empty());
        if (is_nil(q.m_rear)) {
            if (is_nil(cdr(q.m_front))) {
                return mk_pair(queue(), car(q.m_front));
            } else {
                auto p = split_reverse_second(q.m_front);
                return mk_pair(queue(p.first, cdr(p.second)), car(p.second));
            }
        } else {
            return mk_pair(queue(q.m_front, cdr(q.m_rear)), car(q.m_rear));
        }
    }

    class iterator {
        typename list<T>::iterator m_it;
        queue const *              m_queue;
        iterator(typename list<T>::iterator const & it, queue const * queue) {}
    public:
        iterator(iterator const & s):m_it(s.m_it), m_queue(s.m_queue) {}
        iterator & operator++() {
            ++m_it;
            if (m_queue && m_it == m_queue->m_front.end()) {
                m_it    = m_queue->m_rear.begin();
                m_queue = nullptr;
            }
            return *this;
        }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() { return m_it.operator*(); }
        T const * operator->() { return m_it.operator->(); }
    };

    /**
        \brief Return an iterator for the beginning of the queue.
        The iterator traverses the queue in an arbitrary order.
    */
    iterator begin() const { return iterator(m_front.begin(), this); }
    iterator end() const { return iterator(m_rear.end(), nullptr); }
};
/** \brief Return the size of \c q. */
template<typename T> unsigned size(queue<T> const & q) { return q.size(); }
/** \brief Return true iff \c q is empty */
template<typename T> bool is_empty(queue<T> const & q) { return q.is_empty(); }

template<typename T> inline std::ostream & operator<<(std::ostream & out, queue<T> const & q) {
    out << "[";
    queue<T> q2 = q;
    bool first = true;
    while(!is_empty(q2)) {
        auto p = pop_front(q2);
        if (first)
            first = false;
        else
            out << " ";
        out << p.second;
        q2 = p.first;
    }
    out << "]";
    return out;
}
}
