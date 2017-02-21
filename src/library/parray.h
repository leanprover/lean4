/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <memory>
#include <algorithm>
#include "util/memory_pool.h"
#include "util/debug.h"
#include "util/buffer.h"
#include "util/thread.h"

namespace lean {

template<typename T>
class parray {
    enum cell_kind { Set, PushBack, PopBack, Root };

    static size_t capacity(T * vs) {
        return vs == nullptr ? 0 : (reinterpret_cast<size_t*>(vs))[-1];
    }

    static T * allocate_raw_array(size_t c) {
        size_t * mem = static_cast<size_t*>(malloc(sizeof(T)*c + sizeof(size_t)));
        *mem = c;
        ++mem;
        T * r = reinterpret_cast<T*>(mem);
        lean_assert(capacity(r) == c);
        return r;
    }

    static void deallocate_raw_array(T * vs) {
        if (vs == nullptr)
            return;
        size_t * mem = reinterpret_cast<size_t*>(vs);
        --mem;
        free(mem);
    }

    static void deallocate_array(T * vs, size_t sz) {
        std::for_each(vs, vs + sz, [](T & e) { e.~T(); });
        deallocate_raw_array(vs);
    }

    static T * expand(T * vs, size_t sz) {
        size_t curr_capacity = capacity(vs);
        size_t new_capacity  = curr_capacity == 0 ? 2 : (3 * curr_capacity + 1) >> 1;
        T * new_vs           = allocate_raw_array(new_capacity);
        std::uninitialized_copy(vs, vs + sz, new_vs);
        deallocate_array(vs, sz);
        return new_vs;
    }

    struct cell {
        unsigned     m_rc;
        cell_kind    m_kind;
        union {
            size_t   m_idx;
            size_t   m_size;
        };
        T m_elem;
        union {
            cell  * m_next;
            T *     m_values;
        };

        cell_kind kind() const { return static_cast<cell_kind>(m_kind); }
        unsigned idx() const { lean_assert(kind() != Root); return m_idx; }
        unsigned size() const { lean_assert(kind() == Root); return m_size; }
        cell * next() const { lean_assert(kind() != Root); return m_next; }
        T const & elem() const { lean_assert(kind() == Set || kind() == PushBack); return m_elem; }
        cell():m_rc(1), m_kind(Root), m_size(0), m_values(0) {}
    };

    static memory_pool & get_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(sizeof(cell));
        return *g_allocator;
    }

    static void deallocate_cell(cell * c) {
        while (true) {
            cell * next = nullptr;
            switch (c->kind()) {
            case Set:
            case PushBack:
            case PopBack:
                next = c->next();
                break;
            case Root:
                deallocate_array(c->m_values, c->m_size);
                break;
            }
            c->~cell();
            get_allocator().recycle(c);
            if (next == nullptr)
                return;
            lean_assert(next->m_rc > 0);
            next->m_rc--;
            if (next->m_rc > 0)
                return;
            c = next;
        }
    }

    static void inc_ref(cell * c) {
        if (c == nullptr) return;
        c->m_rc++;
    }

    static void dec_ref(cell * c) {
        if (c == nullptr) return;
        lean_assert(c->m_rc > 0);
        c->m_rc--;
        if (c->m_rc == 0)
            deallocate_cell(c);
    }

    static cell * mk_cell() {
        return new (get_allocator().allocate()) cell();
    }

    static void reroot(cell * r) {
        lean_assert(r->m_rc > 0);
        if (r->kind() == Root)
            return;
        buffer<cell *, 1024> cs;
        size_t i = 0;
        cell * c   = r;
        while (c->kind() != Root) {
            cs.push_back(c);
            c = c->next();
            i++;
        }
        cell * last = c;
        size_t sz   = c->m_size;
        T * vs      = c->m_values;
        i           = cs.size();
        while (i > 0) {
            --i;
            cell * p = cs[i];
            lean_assert(p->kind() != Root);
            lean_assert(p->m_next == c);
            switch (p->kind()) {
            case Set:
                c->m_kind    = Set;
                c->m_idx     = p->m_idx;
                c->m_elem    = vs[c->m_idx];
                vs[p->m_idx] = p->m_elem;
                break;
            case PushBack:
                c->m_kind = PopBack;
                if (sz == capacity(vs))
                    vs = expand(vs, sz);
                c->m_idx  = sz;
                vs[sz]    = p->m_elem;
                sz++;
                break;
            case PopBack:
                c->m_kind = PushBack;
                --sz;
                c->m_idx  = sz;
                c->m_elem = vs[sz];
                break;
            case Root:
                lean_unreachable();
                break;
            }
            c->m_next   = p;
            c = p;
        }
        lean_assert(c == r);
        r->m_kind   = Root;
        r->m_values = vs;
        r->m_size   = sz;
        inc_ref(r);
        dec_ref(last);
    }

    static T const & read(cell * c, size_t i) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        lean_assert(i < c->size());
        return c->m_values[i];
    }

    static size_t size(cell * c) {
        if (c->kind() != Root)
            reroot(c);
        return c->size();
    }

    static cell * write(cell * c, size_t i, T const & v) {
        if (c->kind() != Root)
            reroot(c);
        if (c->m_rc == 1) {
            lean_assert(i < c->size());
            c->m_values[i] = v;
            return c;
        } else {
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            c->m_kind             = Set;
            c->m_idx              = i;
            c->m_elem             = new_cell->m_values[i];
            c->m_next             = new_cell;
            c->m_rc--;
            new_cell->m_rc++;
            new_cell->m_values[i] = v;
            return new_cell;
        }
    }

    static void push_back_core(cell * c, T const & v) {
        if (c->m_size == capacity(c->m_values))
            c->m_values = expand(c->m_values, c->m_size);
        new (c->m_values + c->m_size) T(v);
        c->m_size++;
    }

    static cell * push_back(cell * c, T const & v) {
        if (c->kind() != Root)
            reroot(c);
        if (c->m_rc == 1) {
            push_back_core(c, v);
            return c;
        } else {
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            c->m_kind             = PopBack;
            c->m_next             = new_cell;
            c->m_rc--;
            new_cell->m_rc++;
            push_back_core(new_cell, v);
            return new_cell;
        }
    }

    static void pop_back_core(cell * c) {
        lean_assert(c->m_size > 0);
        c->m_size--;
        c->m_values[c->m_size].~T();
    }

    static cell * pop_back(cell * c) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->m_size > 0);
        if (c->m_rc == 1) {
            pop_back_core(c);
            return c;
        } else {
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            c->m_kind             = PushBack;
            c->m_elem             = new_cell->m_values[c->m_size - 1];
            c->m_next             = new_cell;
            c->m_rc--;
            new_cell->m_rc++;
            pop_back_core(new_cell);
            return new_cell;
        }
    }

    cell * m_cell;
public:
    parray():m_cell(mk_cell()) {}
    parray(size_t sz, T const & v):m_cell(mk_cell()) {
        m_cell->m_size   = sz;
        m_cell->m_values = allocate_raw_array(sz);
        std::uninitialized_fill(m_cell->m_values, m_cell->m_values + sz, v);
    }
    parray(parray const & s):m_cell(s.m_cell) { if (m_cell) inc_ref(m_cell); }
    parray(parray && s):m_cell(s.m_cell) { s.m_cell = nullptr; }
    ~parray() { if (m_cell) dec_ref(m_cell); }

    parray & operator=(parray const & s) {
        if (s.m_cell)
            inc_ref(s.m_cell);
        cell * new_cell = s.m_cell;
        if (m_cell)
            dec_ref(m_cell);
        m_cell = new_cell;
        return *this;
    }

    parray & operator=(parray && s) {
        if (m_cell)
            dec_ref(m_cell);
        m_cell = s.m_ptr;
        s.m_ptr = nullptr;
        return *this;
    }

    size_t size() const {
        return size(m_cell);
    }

    T const & operator[](size_t i) const {
        return read(m_cell, i);
    }

    void set(size_t i, T const & v) {
        m_cell = write(m_cell, i, v);
    }

    void push_back(T const & v) {
        m_cell = push_back(m_cell, v);
    }

    void pop_back() {
        m_cell = pop_back(m_cell);
    }

    unsigned get_rc() const {
        return m_cell->m_rc;
    }
};
}
