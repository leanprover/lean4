/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <deque>
#include "rc.h"

#ifndef LEAN_PDEQUE_MIN_QUOTA
#define LEAN_PDEQUE_MIN_QUOTA 16
#endif

namespace lean {
/**
   \brief Deque with O(1) copy operation.
   We call it pdeque because it can be used to simulate persistent deques.

   \remark This class uses the same "trick" used to implement pvector.
*/
template<typename T>
class pdeque {
    enum class cell_kind { PushBack, PopBack, PushFront, PopFront, Set, Root };

    /**
       \brief Base class for representing the data.
       We have two kinds of data: delta and root (the actual deque).
       The deltas store changes to shared deques.
    */
    struct cell {
        cell_kind m_kind;
        MK_LEAN_RC();
        cell(cell_kind k):m_kind(k), m_rc(0) {}
        cell(cell const & c):m_kind(c.m_kind), m_rc(0) {}
        void dealloc();
        unsigned size() const;
        /**
           \brief Return the quota for a cell. When the quota of cell reaches 0, then we perform a deep copy.
        */
        unsigned quota() const;
        cell_kind kind() const { return m_kind; }
    };

    /**
       \brief Cell for wrapping std::deque
    */
    struct root_cell : public cell {
        std::deque<T> m_deque;
        root_cell():cell(cell_kind::Root) {}
    };

    /**
       \brief Base class for storing non-destructive updates: Push, Pop, Set.
       \remark We can view delta_cell's as delayed operations.
    */
    struct delta_cell : public cell {
        unsigned m_size;
        unsigned m_quota;
        cell *   m_prev;
        delta_cell(cell_kind k, unsigned sz, cell * prev):cell(k), m_size(sz), m_quota(prev->quota() - 1), m_prev(prev) {
            lean_assert(m_prev);
            m_prev->inc_ref();
        }
        delta_cell(delta_cell const & c):cell(c), m_size(c.m_size), m_quota(c.m_quota), m_prev(c.m_prev) {
            lean_assert(m_prev);
            m_prev->inc_ref();
        }
        ~delta_cell() { lean_assert(m_prev); m_prev->dec_ref(); }
    };

    /**
       \brief Cell for representing the deque obtained by removing the last element from
       the deque represented by \c prev.
    */
    struct pop_back_cell : public delta_cell {
        pop_back_cell(cell * prev):delta_cell(cell_kind::PopBack, prev->size() - 1, prev) {}
        pop_back_cell(pop_back_cell const & c):delta_cell(c) {}
    };

    /**
       \brief Cell for representing the deque obtained by removing the first element from
       the deque represented by \c prev.
    */
    struct pop_front_cell : public delta_cell {
        pop_front_cell(cell * prev):delta_cell(cell_kind::PopFront, prev->size() - 1, prev) {}
        pop_front_cell(pop_front_cell const & c):delta_cell(c) {}
    };

    /**
       \brief Cell for representing the deque obtained by adding \c v
       to the end of the queue represented by \c prev.
    */
    struct push_back_cell : public delta_cell {
        T m_val;
        push_back_cell(T const & v, cell * prev):delta_cell(cell_kind::PushBack, prev->size() + 1, prev), m_val(v) {}
        push_back_cell(push_back_cell const & c):delta_cell(c), m_val(c.m_val) {}
    };

    /**
       \brief Cell for representing the deque obtained by adding \c v
       to the beginning of the queue represented by \c prev.
    */
    struct push_front_cell : public delta_cell {
        T m_val;
        push_front_cell(T const & v, cell * prev):delta_cell(cell_kind::PushFront, prev->size() + 1, prev), m_val(v) {}
        push_front_cell(push_front_cell const & c):delta_cell(c), m_val(c.m_val) {}
    };

    /**
       \brief Cell for representing the deque obtained by updating position \c i with value \c v
       in the the deque represented by \c prev.
    */
    struct set_cell : public delta_cell {
        unsigned m_idx;
        T        m_val;
        set_cell(unsigned i, T const & v, cell * prev):delta_cell(cell_kind::Set, prev->size(), prev), m_idx(i), m_val(v) {}
        set_cell(set_cell const & c):delta_cell(c), m_idx(c.m_idx), m_val(c.m_val) {}
    };

    static push_back_cell & to_push_back(cell * c) { lean_assert(c->kind() == cell_kind::PushBack); return *static_cast<push_back_cell*>(c); }
    static push_back_cell const & to_push_back(cell const * c) { lean_assert(c->kind() == cell_kind::PushBack); return *static_cast<push_back_cell const *>(c); }
    static push_front_cell & to_push_front(cell * c) { lean_assert(c->kind() == cell_kind::PushFront); return *static_cast<push_front_cell*>(c); }
    static push_front_cell const & to_push_front(cell const * c) { lean_assert(c->kind() == cell_kind::PushFront); return *static_cast<push_front_cell const *>(c); }
    static pop_back_cell & to_pop_back(cell * c) { lean_assert(c->kind() == cell_kind::PopBack); return *static_cast<pop_back_cell*>(c); }
    static pop_back_cell const & to_pop_back(cell const * c) { lean_assert(c->kind() == cell_kind::PopBack); return *static_cast<pop_back_cell const *>(c); }
    static pop_front_cell & to_pop_front(cell * c) { lean_assert(c->kind() == cell_kind::PopFront); return *static_cast<pop_front_cell*>(c); }
    static pop_front_cell const & to_pop_front(cell const * c) { lean_assert(c->kind() == cell_kind::PopFront); return *static_cast<pop_front_cell const *>(c); }
    static set_cell & to_set(cell * c) { lean_assert(c->kind() == cell_kind::Set); return *static_cast<set_cell*>(c); }
    static set_cell const & to_set(cell const * c) { lean_assert(c->kind() == cell_kind::Set); return *static_cast<set_cell const *>(c); }
    static root_cell & to_root(cell * c) { lean_assert(c->kind() == cell_kind::Root); return *static_cast<root_cell*>(c); }
    static root_cell const & to_root(cell const * c) { lean_assert(c->kind() == cell_kind::Root); return *static_cast<root_cell const *>(c); }

    cell * m_ptr;
    pdeque(cell * d):m_ptr(d) { lean_assert(m_ptr); m_ptr->inc_ref(); }

    /** \brief Return true iff the cell associated with this deque is shared */
    bool is_shared() const { return m_ptr->get_rc() > 1; }

    /** \brief Update the cell (and reference counters) of this deque */
    void update_cell(cell * new_cell) {
        lean_assert(new_cell);
        lean_assert(m_ptr);
        new_cell->inc_ref();
        m_ptr->dec_ref();
        m_ptr = new_cell;
    }

    /**
       \brief Auxiliary method for \c flat
       Given an empty deque \c r, then <tt>flat_core(c, r)</tt> will
       store in r the deque represented by cell \c c.
       That is, the deque obtained after finding the root cell (aka wrapper for std::deque),
       and applying all deltas.
    */
    static void flat_core(cell * c, std::deque<T> & r) {
        lean_assert(r.empty());
        switch(c->kind()) {
        case cell_kind::PushBack:
            flat_core(to_push_back(c).m_prev, r);
            r.push_back(to_push_back(c).m_val);
            break;
        case cell_kind::PushFront:
            flat_core(to_push_front(c).m_prev, r);
            r.push_front(to_push_front(c).m_val);
            break;
        case cell_kind::PopBack:
            flat_core(to_pop_back(c).m_prev, r);
            r.pop_back();
            break;
        case cell_kind::PopFront:
            flat_core(to_pop_front(c).m_prev, r);
            r.pop_front();
            break;
        case cell_kind::Set:
            flat_core(to_set(c).m_prev, r);
            r[to_set(c).m_idx] = to_set(c).m_val;
            break;
        case cell_kind::Root:
            r = to_root(c).m_deque;
            break;
        }
    }

    /**
       \brief Change the representation to a root cell.
    */
    void flat() {
        lean_assert(m_ptr->kind() != cell_kind::Root);
        std::deque<T> r;
        flat_core(m_ptr, r);
        update_cell(new root_cell());
        to_root(m_ptr).m_deque.swap(r);
        lean_assert(!is_shared());
    }

    /**
       \brief If the quota associated with m_cell is zero, then
       compute a flat representation. That is, represent the deque
       using a single root_cell.
    */
    void flat_if_needed() {
        lean_assert(m_ptr->kind() != cell_kind::Root);
        if (static_cast<delta_cell*>(m_ptr)->m_quota == 0) {
            flat();
        }
    }

    /**
        \brief Update quota based on the cost of a read
        Return true if the quota was updated, and false
        if the representation had to be updated.
    */
    bool update_quota_on_read(unsigned cost) {
        cost /= 2; // reads are cheaper than writes
        if (cost > 0) {
            if (cost >= m_ptr->quota()) {
                flat();
                return false;
            } else {
                if (is_shared()) {
                    switch (m_ptr->kind()) {
                    case cell_kind::PushBack:  update_cell(new push_back_cell(to_push_back(m_ptr))); break;
                    case cell_kind::PushFront: update_cell(new push_front_cell(to_push_front(m_ptr))); break;
                    case cell_kind::PopBack:   update_cell(new pop_back_cell(to_pop_back(m_ptr))); break;
                    case cell_kind::PopFront:  update_cell(new pop_front_cell(to_pop_front(m_ptr))); break;
                    case cell_kind::Set:       update_cell(new set_cell(to_set(m_ptr))); break;
                    case cell_kind::Root:      lean_unreachable(); break;
                    }
                }
                lean_assert(!is_shared());
                lean_assert(static_cast<delta_cell*>(m_ptr)->m_quota > cost);
                static_cast<delta_cell*>(m_ptr)->m_quota -= cost;
            }
        }
        return true;
    }

    void pop_back_core()  { update_cell(new pop_back_cell(m_ptr)); }
    void pop_front_core() { update_cell(new pop_front_cell(m_ptr)); }
    void push_back_core(T const & v) { update_cell(new push_back_cell(v, m_ptr)); }
    void push_front_core(T const & v) { update_cell(new push_front_cell(v, m_ptr)); }
    void set_core(unsigned i, T const & v) { update_cell(new set_cell(i, v, m_ptr)); }

    bool is_root() const { return m_ptr->kind() == cell_kind::Root; }

public:
    pdeque():m_ptr(new root_cell()) { m_ptr->inc_ref(); }
    pdeque(pdeque const & s):m_ptr(s.m_ptr) { m_ptr->inc_ref(); }
    pdeque(pdeque && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~pdeque() { if (m_ptr) m_ptr->dec_ref(); }

    pdeque & operator=(pdeque const & s) { LEAN_COPY_REF(pdeque, s); }
    pdeque & operator=(pdeque && s) { LEAN_MOVE_REF(pdeque, s); }

    /** \brief Return the number of elements */
    unsigned size() const { return m_ptr->size(); }

    /** \brief Check whether the container is empty */
    bool empty() const { return size() == 0; }

    /**
        \brief Access specified element
        \pre i < size()
    */
    T const & operator[](unsigned i) const {
        lean_assert(i < size());
        cell const * it = m_ptr;
        unsigned input_i = i;
        unsigned cost = 0;
        while (true) {
            switch (it->kind()) {
            case cell_kind::PushBack:
                if (i + 1 == to_push_back(it).m_size) {
                    if (const_cast<pdeque*>(this)->update_quota_on_read(cost))
                        return to_push_back(it).m_val;
                    else
                        return operator[](input_i); // representation was updated
                }
                break;
            case cell_kind::PushFront:
                if (i == 0) {
                    if (const_cast<pdeque*>(this)->update_quota_on_read(cost))
                        return to_push_front(it).m_val;
                    else
                        return operator[](input_i); // representation was updated
                } else {
                    i--;
                }
                break;
            case cell_kind::PopBack:
                break;
            case cell_kind::PopFront:
                i++;
                break;
            case cell_kind::Set:
                if (to_set(it).m_idx == i) {
                    if (const_cast<pdeque*>(this)->update_quota_on_read(cost))
                        return to_set(it).m_val;
                    else
                        return operator[](input_i); // representation was updated
                }
                break;
            case cell_kind::Root:
                if (const_cast<pdeque*>(this)->update_quota_on_read(cost))
                    return to_root(it).m_deque[i];
                else
                    return operator[](input_i); // representation was updated
            }
            it = static_cast<delta_cell const *>(it)->m_prev;
            cost++;
        }
    }

    /**
        \brief Return the last element in the deque
        \pre !empty()
    */
    T const & back() const {
        lean_assert(!empty());
        return operator[](size() - 1);
    }

    /**
        \brief Return the first element in the deque
        \pre !empty()
    */
    T const & front() const {
        lean_assert(!empty());
        return operator[](0);
    }

    /**
       \brief Add an element to the end of the deque
    */
    void push_back(T const & v) {
        if (!is_root())
            flat_if_needed();
        switch (m_ptr->kind()) {
        case cell_kind::PushBack: case cell_kind::PushFront: case cell_kind::PopBack:
        case cell_kind::PopFront: case cell_kind::Set:
            push_back_core(v);
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_deque.push_back(v);
            else
                push_back_core(v);
            break;
        }
    }

    /**
       \brief Add an element in the beginning of the deque
    */
    void push_front(T const & v) {
        if (!is_root())
            flat_if_needed();
        switch (m_ptr->kind()) {
        case cell_kind::PushBack: case cell_kind::PushFront: case cell_kind::PopBack:
        case cell_kind::PopFront: case cell_kind::Set:
            push_front_core(v);
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_deque.push_front(v);
            else
                push_front_core(v);
            break;
        }
    }

    /**
       \brief Remove the last element
       \pre !empty()
    */
    void pop_back() {
        lean_assert(!empty());
        if (!is_root())
            flat_if_needed();
        switch (m_ptr->kind()) {
        case cell_kind::PushBack:
            update_cell(to_push_back(m_ptr).m_prev);
            break;
        case cell_kind::PushFront: case cell_kind::PopBack:
        case cell_kind::PopFront: case cell_kind::Set:
            pop_back_core();
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_deque.pop_back();
            else
                pop_back_core();
            break;
        }
    }

    /**
       \brief Remove the first element
       \pre !empty()
    */
    void pop_front() {
        lean_assert(!empty());
        if (!is_root())
            flat_if_needed();
        switch (m_ptr->kind()) {
        case cell_kind::PushFront:
            update_cell(to_push_front(m_ptr).m_prev);
            break;
        case cell_kind::PushBack: case cell_kind::PopBack:
        case cell_kind::PopFront: case cell_kind::Set:
            pop_front_core();
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_deque.pop_front();
            else
                pop_front_core();
            break;
        }
    }

    /**
       \brief Update position \c i with value \c v
       \pre i < size()
    */
    void set(unsigned i, T const & v) {
        lean_assert(i < size());
        if (!is_root())
            flat_if_needed();
        switch (m_ptr->kind()) {
        case cell_kind::PushBack:
        case cell_kind::PopBack:
            set_core(i, v);
            break;
        case cell_kind::Set:
            if (!is_shared() && i == to_set(m_ptr).m_idx)
                to_set(m_ptr).m_val = v;
            else
                set_core(i, v);
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_deque[i] = v;
            else
                set_core(i, v);
            break;
        }
    }

    class iterator {
        friend class pdeque;
        pdeque const & m_deque;
        unsigned       m_it;
        iterator(pdeque const & v, unsigned it):m_deque(v), m_it(it) {}
    public:
        iterator(iterator const & s):m_deque(s.m_deque), m_it(s.m_it) {}
        iterator & operator++() { ++m_it; return *this; }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { lean_assert(&m_deque == &(s.m_deque)); return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() const { return m_deque[m_it]; }
        T const * operator->() const { return &(m_deque[m_it]); }
    };

    /** \brief Return an iterator to the beginning */
    iterator begin() const { return iterator(*this, 0); }
    /** \brief Return an iterator to the end */
    iterator end() const { return iterator(*this, size()); }
};

template<typename T>
void pdeque<T>::cell::dealloc() {
    switch (kind()) {
    case cell_kind::PushBack:  delete static_cast<push_back_cell*>(this);  break;
    case cell_kind::PushFront: delete static_cast<push_front_cell*>(this); break;
    case cell_kind::PopBack:   delete static_cast<pop_back_cell*>(this);   break;
    case cell_kind::PopFront:  delete static_cast<pop_front_cell*>(this);  break;
    case cell_kind::Set:       delete static_cast<set_cell*>(this);        break;
    case cell_kind::Root:      delete static_cast<root_cell*>(this);       break;
    }
}

template<typename T>
unsigned pdeque<T>::cell::size() const {
    if (kind() == cell_kind::Root) {
        return static_cast<root_cell const *>(this)->m_deque.size();
    } else {
        return static_cast<delta_cell const *>(this)->m_size;
    }
}

template<typename T>
unsigned pdeque<T>::cell::quota() const {
    if (kind() == cell_kind::Root) {
        unsigned sz = size();
        if (sz < LEAN_PDEQUE_MIN_QUOTA)
            return LEAN_PDEQUE_MIN_QUOTA;
        else
            return sz;
    } else {
        return static_cast<delta_cell const *>(this)->m_quota;
    }
}

/** \brief Non-destructive push_back. It is simulated using O(1) copy. */
template<typename T>
pdeque<T> push_back(pdeque<T> const & s, T const & v) { pdeque<T> r(s); r.push_back(v); return r; }
/** \brief Non-destructive push_front. It is simulated using O(1) copy. */
template<typename T>
pdeque<T> push_front(pdeque<T> const & s, T const & v) { pdeque<T> r(s); r.push_front(v); return r; }
/** \brief Non-destructive pop_back. It is simulated using O(1) copy. */
template<typename T>
pdeque<T> pop_back(pdeque<T> const & s) { pdeque<T> r(s); r.pop_back(); return r; }
/** \brief Non-destructive pop_front. It is simulated using O(1) copy. */
template<typename T>
pdeque<T> pop_front(pdeque<T> const & s) { pdeque<T> r(s); r.pop_front(); return r; }
/** \brief Non-destructive set. It is simulated using O(1) copy. */
template<typename T>
pdeque<T> set(pdeque<T> const & s, unsigned i, T const & v) { pdeque<T> r(s); r.set(i, v); return r; }
/** \brief Return the last element of \c s. */
template<typename T>
T const & back(pdeque<T> const & s) { return s.back(); }
/** \brief Return the first element of \c s. */
template<typename T>
T const & front(pdeque<T> const & s) { return s.front(); }
/** \brief Return true iff \c s is empty. */
template<typename T>
bool empty(pdeque<T> const & s) { return s.empty(); }
/** \brief Return the size of s. */
template<typename T>
unsigned size(pdeque<T> const & s) { return s.size(); }

template<typename T> inline std::ostream & operator<<(std::ostream & out, pdeque<T> const & d) {
    out << "[[";
    bool first = true;
    auto it  = d.begin();
    auto end = d.end();
    for (; it != end; ++it) {
        if (first)
            first = false;
        else
            out << ", ";
        out << *it;
    }
    out << "]]";
    return out;
}
}
