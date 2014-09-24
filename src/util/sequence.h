/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rc.h"
#include "util/debug.h"
#include "util/buffer.h"
#include "util/optional.h"
#include "util/memory_pool.h"
#include "util/list.h"

namespace lean {
/** \brief Sequence datastructure with O(1) concatenation operation */
template<typename T>
class sequence {
    struct cell {
        bool m_join;
        MK_LEAN_RC();
        void dealloc();
        cell(bool join):m_join(join), m_rc(1) {}
    };

    struct elem_cell : public cell {
        T m_value;
        elem_cell(T const & v):cell(false), m_value(v) {}
    };

    struct node {
        cell * m_ptr;
        node():m_ptr(nullptr) {}
        explicit node(T const & v);
        node(node const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
        node(node && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
        node(node const & f, node const & s);
        ~node() { if (m_ptr) m_ptr->dec_ref(); }
        node & operator=(node const & s) { LEAN_COPY_REF(s); }
        node & operator=(node && s) { LEAN_MOVE_REF(s); }
        cell * raw() const { return m_ptr; }
        explicit operator bool() const { return m_ptr != nullptr; }
    };

    struct join_cell : public cell {
        node m_first;
        node m_second;
        join_cell(node const & f, node const & s):cell(true), m_first(f), m_second(s) {}
    };

    static memory_pool & get_elem_cell_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(sizeof(elem_cell));
        return *g_allocator;
    }

    static memory_pool & get_join_cell_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(sizeof(join_cell));
        return *g_allocator;
    }

private:
    node m_node;
public:
    sequence() {}
    explicit sequence(T const & v):m_node(v) {}
    sequence(sequence const & f, sequence const & s):m_node(f.m_node, s.m_node) {}

    /** \brief Return true iff it is not the empty/nil sequence. */
    explicit operator bool() const { return m_node.raw() != nullptr; }

    /** \brief Pointer equality. Return true iff \c s1 and \c s2 point to the same memory location. */
    friend bool is_eqp(sequence const & s1, sequence const & s2) { return s1.m_node.raw() == s2.m_node.raw(); }

    friend sequence operator+(sequence const & s1, sequence const & s2) { return sequence(s1, s2); }
    friend sequence operator+(sequence const & s, T const & v) { return s + sequence(v); }
    friend sequence operator+(T const & v, sequence const & s) { return sequence(v) + s; }
    sequence & operator+=(T const & v) { *this = *this + v; return *this; }
    sequence & operator+=(sequence const & s) { *this = *this + s; return *this; }

    template<typename F>
    bool all_of(F && f) const {
        buffer<cell const *> todo;
        if (m_node) todo.push_back(m_node.raw());
        while (!todo.empty()) {
            cell const * c = todo.back();
            todo.pop_back();
            if (c->m_join) {
                todo.push_back(static_cast<join_cell const *>(c)->m_second.raw());
                todo.push_back(static_cast<join_cell const *>(c)->m_first.raw());
            } else {
                if (!f(static_cast<elem_cell const *>(c)->m_value))
                    return false;
            }
        }
        return true;
    }

    template<typename F>
    void for_each(F && f) const { all_of([&](T const & v) { f(v); return true; }); }

    /** \brief Store sequence elements in \c r */
    void linearize(buffer<T> & r) const { for_each([&](T const & v) { r.push_back(v); }); }

    list<T> to_list() const {
        buffer<T> tmp;
        linearize(tmp);
        return ::lean::to_list(tmp.begin(), tmp.end());
    }
};

template<typename T>
void sequence<T>::cell::dealloc() {
    if (m_join) {
        join_cell * c = static_cast<join_cell*>(this);
        c->~join_cell();
        get_join_cell_allocator().recycle(c);
    } else {
        elem_cell * c = static_cast<elem_cell*>(this);
        c->~elem_cell();
        get_elem_cell_allocator().recycle(c);
    }
}

template<typename T>
sequence<T>::node::node(T const & v):m_ptr(new (get_elem_cell_allocator().allocate()) elem_cell(v)) {}

template<typename T>
sequence<T>::node::node(node const & f, node const & s) {
    if (f && s) {
        m_ptr = new (get_join_cell_allocator().allocate()) join_cell(f, s);
    } else if (f) {
        m_ptr = f.m_ptr;
        m_ptr->inc_ref();
    } else if (s) {
        m_ptr = s.m_ptr;
        m_ptr->inc_ref();
    } else {
        m_ptr = nullptr;
    }
}
}
