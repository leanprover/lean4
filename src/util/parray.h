/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <vector>
#include <algorithm>
#include "util/rc.h"
#include "util/debug.h"
#include "util/buffer.h"
#include "util/memory_pool.h"

#ifndef LEAN_PARRAY_MAX_READ_TRAIL_SZ
#define LEAN_PARRAY_MAX_READ_TRAIL_SZ 128
#endif

namespace lean {
/** \brief Persistent arrays */
template<typename T> class parray {
    enum cell_kind { SET, PUSH_BACK, POP_BACK, ROOT };
    struct cell {
        MK_LEAN_RC();
        cell_kind m_kind;
        cell(cell_kind k):m_rc(0), m_kind(k) {}
        void dealloc();
    };

    typedef parray ref;

    struct root_cell : public cell {
        std::vector<T> m_data;

        root_cell():cell(ROOT) {}
        root_cell(std::vector<T> const & d):cell(ROOT), m_data(d) {}

        static memory_pool & get_allocator() {
            LEAN_THREAD_PTR(memory_pool, g_allocator);
            if (!g_allocator)
                g_allocator = allocate_thread_memory_pool(sizeof(root_cell));
            return *g_allocator;
        }

        void dealloc_root() {
            this->~root_cell();
            get_allocator().recycle(this);
        }
    };

    struct step_cell : public cell {
        unsigned m_size;
        ref      m_next;

        step_cell(cell_kind k, unsigned s, ref const & r):
            cell(k), m_size(s), m_next(r) {}

        cell * dec_ref_next() {
            if (m_next.m_ptr) {
                cell * c = m_next.steal_ptr();
                lean_assert(!(m_next.m_ptr));
                if (c->dec_ref_core())
                    return c;
            }
            return nullptr;
        }
    };

    struct pop_back_cell : public step_cell {
        pop_back_cell(ref const & n):
            step_cell(POP_BACK, n.size() - 1, n) {}

        static memory_pool & get_allocator() {
            LEAN_THREAD_PTR(memory_pool, g_allocator);
            if (!g_allocator)
                g_allocator = allocate_thread_memory_pool(sizeof(pop_back_cell));
            return *g_allocator;
        }

        cell * dealloc_pop_back() {
            cell * r = this->dec_ref_next();
            this->~pop_back_cell();
            get_allocator().recycle(this);
            return r;
        }
    };

    struct push_back_cell : public step_cell {
        T m_value;

        static memory_pool & get_allocator() {
            LEAN_THREAD_PTR(memory_pool, g_allocator);
            if (!g_allocator)
                g_allocator = allocate_thread_memory_pool(sizeof(push_back_cell));
            return *g_allocator;
        }

        push_back_cell(T const & v, ref const & n):
            step_cell(PUSH_BACK, n.size() + 1, n), m_value(v) {}

        cell * dealloc_push_back() {
            cell * r = this->dec_ref_next();
            this->~push_back_cell();
            get_allocator().recycle(this);
            return r;
        }
    };

    struct set_cell : public step_cell {
        unsigned m_idx;
        T        m_value;

        static memory_pool & get_allocator() {
            LEAN_THREAD_PTR(memory_pool, g_allocator);
            if (!g_allocator)
                g_allocator = allocate_thread_memory_pool(sizeof(set_cell));
            return *g_allocator;
        }

        set_cell(unsigned idx, T const & v, ref const & n):
            step_cell(SET, n.size(), n), m_idx(idx), m_value(v) {}

        cell * dealloc_set() {
            cell * r = this->dec_ref_next();
            this->~set_cell();
            get_allocator().recycle(this);
            return r;
        }
    };

    cell * m_ptr;
    cell * steal_ptr() { cell * r = m_ptr; m_ptr = nullptr; return r; }

    static root_cell * to_root(cell * c) {
        lean_assert(c->m_kind == ROOT); return static_cast<root_cell*>(c);
    }
    static step_cell * to_step(cell * c) {
        lean_assert(c->m_kind != ROOT); return static_cast<step_cell*>(c);
    }
    static push_back_cell * to_push_back(cell * c) {
        lean_assert(c->m_kind == PUSH_BACK); return static_cast<push_back_cell*>(c);
    }
    static pop_back_cell * to_pop_back(cell * c) {
        lean_assert(c->m_kind == POP_BACK); return static_cast<pop_back_cell*>(c);
    }
    static set_cell * to_set(cell * c) {
        lean_assert(c->m_kind == SET); return static_cast<set_cell*>(c);
    }

public:
    parray():m_ptr(nullptr) {}
    parray(cell * ptr):m_ptr(ptr) { if (m_ptr) ptr->inc_ref(); }
    parray(parray const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    parray(parray && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~parray() { if (m_ptr) m_ptr->dec_ref(); }
    parray & operator=(parray const & n) { LEAN_COPY_REF(n); }
    parray & operator=(parray&& n) { LEAN_MOVE_REF(n); }
    operator bool() const { return m_ptr != nullptr; }
    bool is_shared() const { return m_ptr && m_ptr->get_rc() > 1; }
    cell_kind kind() const { return m_ptr->m_kind; }
    cell * operator->() const { lean_assert(m_ptr); return m_ptr; }
    friend bool is_eqp(parray const & n1, parray const & n2) { return n1.m_ptr == n2.m_ptr; }
    friend void swap(parray & n1, parray & n2) { std::swap(n1.m_ptr, n2.m_ptr); }
    parray steal() { parray r; swap(r, *this); return r; }

    unsigned size() const {
        if (m_ptr == nullptr)
            return 0;
        else if (m_ptr->m_kind == ROOT)
            return to_root(m_ptr)->m_data.size();
        else
            return to_step(m_ptr)->m_size;
    }

    bool empty() const { return size() == 0; }

    void push_back(T const & t) {
        if (!m_ptr) {
            *this = parray(new root_cell());
            to_root(m_ptr)->m_data.push_back(t);
        } else if (m_ptr->get_rc() == 1 && kind() == ROOT) {
            to_root(m_ptr)->m_data.push_back(t);
        } else {
            *this = parray(new push_back_cell(t, *this));
        }
    }

    void set(unsigned idx, T const & t) {
        lean_assert(idx < size());
        if (m_ptr->get_rc() == 1 && kind() == ROOT) {
            to_root(m_ptr)->m_data[idx] = t;
        } else {
            *this = parray(new set_cell(idx, t, *this));
        }
    }

    void pop_back() {
        lean_assert(m_ptr);
        if (m_ptr->get_rc() == 1 && kind() == ROOT) {
            to_root(m_ptr)->m_data.pop_back();
        } else {
            *this = parray(new pop_back_cell(*this));
        }
    }

    void compress() {
        if (!m_ptr) {
            *this = parray(new root_cell());
            return;
        }
        if (m_ptr->m_kind == ROOT)
            return;
        bool shared = false;
        buffer<cell*> cells;
        cell * c     = m_ptr;
        ref r;
        while (true) {
            if (c == nullptr) {
                r = parray(new root_cell());
                break;
            }
            if (c->get_rc() > 1)
                shared = true;
            if (c->m_kind == ROOT) {
                if (!shared) {
                    lean_assert(!cells.empty());
                    r = to_step(cells.back())->m_next.steal();
                } else {
                    r = parray(new root_cell(to_root(c)->m_data));
                }
                break;
            } else {
                cells.push_back(c);
                c = to_step(c)->m_next.m_ptr;
            }
        }
        std::vector<T> & v = to_root(r.m_ptr)->m_data;
        unsigned i = cells.size();
        while (i > 0) {
            --i;
            cell * curr = cells[i];
            switch (curr->m_kind) {
            case SET:
                v[to_set(curr)->m_idx] = to_set(curr)->m_value;
                break;
            case PUSH_BACK:
                v.push_back(to_push_back(curr)->m_value);
                break;
            case POP_BACK:
                v.pop_back();
                break;
            case ROOT:
                lean_unreachable();
            }
        }
        swap(*this, r);
    }

    std::vector<T> const & as_vector() {
        compress();
        return to_root(m_ptr)->m_data;
    }

    std::vector<T> const & as_vector_if_compressed() const {
        lean_assert(is_compressed());
        return to_root(m_ptr)->m_data;
    }

    T const & read(unsigned idx, unsigned max_trail_sz = LEAN_PARRAY_MAX_READ_TRAIL_SZ) const {
        lean_assert(idx < size());
        cell * c = m_ptr;
        unsigned counter = 0;
        while (true) {
            counter++;
            if (counter > max_trail_sz) {
                const_cast<parray*>(this)->compress();
                return to_root(m_ptr)->m_data[idx];
            }
            lean_assert(c);
            switch (c->m_kind) {
            case SET:
                if (to_set(c)->m_idx == idx) {
                    return to_set(c)->m_value;
                }
                c = to_step(c)->m_next.m_ptr;
                break;
            case PUSH_BACK:
                if (idx + 1 == to_step(c)->m_size)
                    return to_push_back(c)->m_value;
                c = to_step(c)->m_next.m_ptr;
                break;
            case POP_BACK:
                c = to_step(c)->m_next.m_ptr;
                break;
            case ROOT:
                return to_root(c)->m_data[idx];
            }
        }
    }

    T const & operator[](unsigned idx) const {
        return read(idx);
    }

    bool is_compressed() const {
        return m_ptr && m_ptr->m_kind == ROOT;
    }

    void display_internal(std::ostream & out) const {
        out << "PARRAY\n";
        cell * c = m_ptr;
        while (c != nullptr) {
            switch (c->m_kind) {
            case SET:
                out << to_set(c)->m_idx << " := " << to_set(c)->m_value << "\n";
                c = to_step(c)->m_next.m_ptr;
                break;
            case PUSH_BACK:
                out << "push_back " << to_push_back(c)->m_value << "\n";
                c = to_step(c)->m_next.m_ptr;
                break;
            case POP_BACK:
                out << "pop_back\n";
                c = to_step(c)->m_next.m_ptr;
                break;
            case ROOT:
                out << "[";
                bool first = true;
                for (T const & v : to_root(c)->m_data) {
                    if (first) first = false; else out << ", ";
                    out << v;
                }
                out << "]\n";
                c = nullptr;
                break;
            }
        }
        out << "END\n";
    }

    void display(std::ostream & out) const {
        out << "[";
        bool first = true;
        for (unsigned i = 0; i < size(); i++) {
            if (first) first = false; else out << ", ";
            out << operator[](i);
        }
        out << "]";
    }
};

template<typename T>
void parray<T>::cell::dealloc() {
    cell * it = this;
    while (it != nullptr) {
        switch (it->m_kind) {
        case SET:
            it = to_set(it)->dealloc_set();
            break;
        case PUSH_BACK:
            it = to_push_back(it)->dealloc_push_back();
            break;
        case POP_BACK:
            it = to_pop_back(it)->dealloc_pop_back();
            break;
        case ROOT:
            to_root(it)->dealloc_root();
            return;
        }
    }
}
}
