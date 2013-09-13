/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <vector>
#include "util/rc.h"

#ifndef LEAN_PVECTOR_MIN_QUOTA
#define LEAN_PVECTOR_MIN_QUOTA 16
#endif

namespace lean {
/**
   \brief Vector with O(1) copy operation.
   We call it pvector because it can be used to simulate persistent vectors.
*/
template<typename T>
class pvector {
    enum class cell_kind { PushBack, PopBack, Set, Root };

    /**
       \brief Base class for representing the data.
       We have two kinds of data: delta and root (the actual vector).
       The deltas store changes to shared vectors.
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
       \brief Cell for wrapping std::vector
    */
    struct root_cell : public cell {
        std::vector<T> m_vector;
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
       \brief Cell for representing the vector obtained by removing the last element from
       the vector represented by \c prev.
    */
    struct pop_cell : public delta_cell {
        pop_cell(cell * prev):delta_cell(cell_kind::PopBack, prev->size() - 1, prev) {}
        pop_cell(pop_cell const & c):delta_cell(c) {}
    };

    /**
       \brief Cell for representing the vector obtained by adding \c v
       to the vector represented by \c prev.
    */
    struct push_cell : public delta_cell {
        T m_val;
        push_cell(T const & v, cell * prev):delta_cell(cell_kind::PushBack, prev->size() + 1, prev), m_val(v) {}
        push_cell(push_cell const & c):delta_cell(c), m_val(c.m_val) {}
    };

    /**
       \brief Cell for representing the vector obtained by updating position \c i with value \c v
       in the the vector represented by \c prev.
    */
    struct set_cell : public delta_cell {
        unsigned m_idx;
        T        m_val;
        set_cell(unsigned i, T const & v, cell * prev):delta_cell(cell_kind::Set, prev->size(), prev), m_idx(i), m_val(v) {}
        set_cell(set_cell const & c):delta_cell(c), m_idx(c.m_idx), m_val(c.m_val) {}
    };

    static push_cell & to_push(cell * c) { lean_assert(c->kind() == cell_kind::PushBack); return *static_cast<push_cell*>(c); }
    static push_cell const & to_push(cell const * c) { lean_assert(c->kind() == cell_kind::PushBack); return *static_cast<push_cell const *>(c); }
    static pop_cell & to_pop(cell * c) { lean_assert(c->kind() == cell_kind::PopBack); return *static_cast<pop_cell*>(c); }
    static pop_cell const & to_pop(cell const * c) { lean_assert(c->kind() == cell_kind::PopBack); return *static_cast<pop_cell const *>(c); }
    static set_cell & to_set(cell * c) { lean_assert(c->kind() == cell_kind::Set); return *static_cast<set_cell*>(c); }
    static set_cell const & to_set(cell const * c) { lean_assert(c->kind() == cell_kind::Set); return *static_cast<set_cell const *>(c); }
    static root_cell & to_root(cell * c) { lean_assert(c->kind() == cell_kind::Root); return *static_cast<root_cell*>(c); }
    static root_cell const & to_root(cell const * c) { lean_assert(c->kind() == cell_kind::Root); return *static_cast<root_cell const *>(c); }

    cell * m_ptr;
    pvector(cell * d):m_ptr(d) { lean_assert(m_ptr); m_ptr->inc_ref(); }

    /** \brief Return true iff the cell associated with this vector is shared */
    bool is_shared() const { return m_ptr->get_rc() > 1; }

    /** \brief Update the cell (and reference counters) of this vector */
    void update_cell(cell * new_cell) {
        lean_assert(new_cell);
        lean_assert(m_ptr);
        new_cell->inc_ref();
        m_ptr->dec_ref();
        m_ptr = new_cell;
    }

    /**
       \brief Auxiliary method for \c flat
       Given an empty vector \c r, then <tt>flat_core(c, r)</tt> will
       store in r the vector represented by cell \c c.
       That is, the vector obtained after finding the root cell (aka wrapper for std::vector),
       and applying all deltas.
    */
    static void flat_core(cell * c, std::vector<T> & r) {
        lean_assert(r.empty());
        switch (c->kind()) {
        case cell_kind::PushBack:
            flat_core(to_push(c).m_prev, r);
            r.push_back(to_push(c).m_val);
            break;
        case cell_kind::PopBack:
            flat_core(to_pop(c).m_prev, r);
            r.pop_back();
            break;
        case cell_kind::Set:
            flat_core(to_set(c).m_prev, r);
            r[to_set(c).m_idx] = to_set(c).m_val;
            break;
        case cell_kind::Root:
            r = to_root(c).m_vector;
            break;
        }
    }

    /**
       \brief Change the representation to a root cell.
    */
    void flat() {
        lean_assert(m_ptr->kind() != cell_kind::Root);
        std::vector<T> r;
        flat_core(m_ptr, r);
        update_cell(new root_cell());
        to_root(m_ptr).m_vector.swap(r);
        lean_assert(!is_shared());
    }

    /**
       \brief If the quota associated with m_cell is zero, then
       compute a flat representation. That is, represent the vector
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
                    case cell_kind::PushBack: update_cell(new push_cell(to_push(m_ptr))); break;
                    case cell_kind::PopBack:  update_cell(new pop_cell(to_pop(m_ptr))); break;
                    case cell_kind::Set:      update_cell(new set_cell(to_set(m_ptr))); break;
                    case cell_kind::Root:     lean_unreachable(); break;
                    }
                }
                lean_assert(!is_shared());
                lean_assert(cost < static_cast<delta_cell*>(m_ptr)->m_quota);
                static_cast<delta_cell*>(m_ptr)->m_quota -= cost;
            }
        }
        return true;
    }

    void pop_back_core() { update_cell(new pop_cell(m_ptr)); }

    void push_back_core(T const & v) { update_cell(new push_cell(v, m_ptr)); }

    void set_core(unsigned i, T const & v) { update_cell(new set_cell(i, v, m_ptr)); }

    bool is_root() const { return m_ptr->kind() == cell_kind::Root; }

public:
    pvector():m_ptr(new root_cell()) { m_ptr->inc_ref(); }
    pvector(pvector const & s):m_ptr(s.m_ptr) { m_ptr->inc_ref(); }
    pvector(pvector && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~pvector() { if (m_ptr) m_ptr->dec_ref(); }

    pvector & operator=(pvector const & s) { LEAN_COPY_REF(pvector, s); }
    pvector & operator=(pvector && s) { LEAN_MOVE_REF(pvector, s); }

    /** \brief Return the number of elements */
    unsigned size() const { return m_ptr->size(); }

    /** \brief Check whether the container is empty */
    bool empty() const { return size() == 0; }

    /**
        \brief Access specified element
        \pre i < size()
    */
    T const & get(unsigned i) const {
        lean_assert(i < size());
        cell const * it = m_ptr;
        unsigned cost = 0;
        while (true) {
            switch (it->kind()) {
            case cell_kind::PushBack:
                if (i + 1 == to_push(it).m_size) {
                    if (const_cast<pvector*>(this)->update_quota_on_read(cost))
                        return to_push(it).m_val;
                    else
                        return get(i); // representation was changed, \c it may have been deleted
                }
                break;
            case cell_kind::PopBack:
                break;
            case cell_kind::Set:
                if (to_set(it).m_idx == i) {
                    if (const_cast<pvector*>(this)->update_quota_on_read(cost))
                        return to_set(it).m_val;
                    else
                        return get(i); // representation was changed, \c it may have been deleted
                }
                break;
            case cell_kind::Root:
                if (const_cast<pvector*>(this)->update_quota_on_read(cost))
                    return to_root(it).m_vector[i];
                else
                    return get(i); // representation was changed, \c it may have been deleted
            }
            it = static_cast<delta_cell const *>(it)->m_prev;
            cost++;
        }
    }

    /**
        \brief Return the last element in the vector
        \pre !empty()
    */
    T const & back() const {
        lean_assert(!empty());
        return operator[](size() - 1);
    }

    /**
       \brief Add an element to the end of the vector
    */
    void push_back(T const & v) {
        if (!is_root())
            flat_if_needed();
        switch (m_ptr->kind()) {
        case cell_kind::PushBack: case cell_kind::Set: case cell_kind::PopBack:
            push_back_core(v);
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_vector.push_back(v);
            else
                push_back_core(v);
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
            update_cell(to_push(m_ptr).m_prev);
            break;
        case cell_kind::Set: case cell_kind::PopBack:
            pop_back_core();
            break;
        case cell_kind::Root:
            if (!is_shared())
                to_root(m_ptr).m_vector.pop_back();
            else
                pop_back_core();
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
                to_root(m_ptr).m_vector[i] = v;
            else
                set_core(i, v);
            break;
        }
    }

    class ref {
        pvector  & m_vector;
        unsigned   m_idx;
    public:
        ref(pvector & v, unsigned i):m_vector(v), m_idx(i) {}
        ref & operator=(T const & a) { m_vector.set(m_idx, a); return *this; }
        operator T const &() const { return m_vector.get(m_idx); }
        T const * operator->() const { return &(m_vector.get(m_idx)); }
    };

    T const & operator[](unsigned i) const { return get(i); }

    ref operator[](unsigned i) { return ref(*this, i); }

    class iterator {
        friend class pvector;
        pvector const & m_vector;
        unsigned        m_it;
        iterator(pvector const & v, unsigned it):m_vector(v), m_it(it) {}
    public:
        iterator(iterator const & s):m_vector(s.m_vector), m_it(s.m_it) {}
        iterator & operator++() { ++m_it; return *this; }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { lean_assert(&m_vector == &(s.m_vector)); return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() const { return m_vector[m_it]; }
        T const * operator->() const { return &(m_vector[m_it]); }
    };

    /** \brief Return an iterator to the beginning */
    iterator begin() const { return iterator(*this, 0); }
    /** \brief Return an iterator to the end */
    iterator end() const { return iterator(*this, size()); }
};

template<typename T>
void pvector<T>::cell::dealloc() {
    switch (kind()) {
    case cell_kind::PushBack: delete static_cast<push_cell*>(this); break;
    case cell_kind::PopBack:  delete static_cast<pop_cell*>(this);  break;
    case cell_kind::Set:   delete static_cast<set_cell*>(this); break;
    case cell_kind::Root:     delete static_cast<root_cell*>(this); break;
    }
}

template<typename T>
unsigned pvector<T>::cell::size() const {
    switch (kind()) {
    case cell_kind::PushBack: case cell_kind::PopBack: case cell_kind::Set:
        return static_cast<delta_cell const *>(this)->m_size;
    case cell_kind::Root:
        return static_cast<root_cell const *>(this)->m_vector.size();
    }
    lean_unreachable();
    return 0;
}

template<typename T>
unsigned pvector<T>::cell::quota() const {
    switch (kind()) {
    case cell_kind::PushBack: case cell_kind::PopBack: case cell_kind::Set:
        return static_cast<delta_cell const *>(this)->m_quota;
    case cell_kind::Root: {
        unsigned sz = size();
        if (sz < LEAN_PVECTOR_MIN_QUOTA)
            return LEAN_PVECTOR_MIN_QUOTA;
        else
            return sz;
    }
    }
    lean_unreachable();
    return 0;
}

/** \brief Non-destructive push_back. It is simulated using O(1) copy. */
template<typename T>
pvector<T> push_back(pvector<T> const & s, T const & v) { pvector<T> r(s); r.push_back(v); return r; }
/** \brief Non-destructive pop_back. It is simulated using O(1) copy. */
template<typename T>
pvector<T> pop_back(pvector<T> const & s) { pvector<T> r(s); r.pop_back(); return r; }
/** \brief Non-destructive set. It is simulated using O(1) copy. */
template<typename T>
pvector<T> set(pvector<T> const & s, unsigned i, T const & v) { pvector<T> r(s); r.set(i, v); return r; }
/** \brief Return the last element of \c s. */
template<typename T>
T const & back(pvector<T> const & s) { return s.back(); }
/** \brief Return true iff \c s is empty. */
template<typename T>
bool empty(pvector<T> const & s) { return s.empty(); }
/** \brief Return the size of \c s. */
template<typename T>
unsigned size(pvector<T> const & s) { return s.size(); }

template<typename T> inline std::ostream & operator<<(std::ostream & out, pvector<T> const & d) {
    out << "[";
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
    out << "]";
    return out;
}
}
