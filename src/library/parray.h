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
#include "library/trace.h"

namespace lean {
// TODO(Leo) add compilation flag for enabling this trace message
#define lean_array_trace(CODE) lean_trace(name({"array", "update"}), CODE)

template<typename T, bool ThreadSafe = false>
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
        atomic<unsigned> m_rc;
        cell_kind        m_kind;
        union {
            size_t       m_idx;
            size_t       m_size;
        };
        cell  *          m_next;
        union {
            T *          m_values; /* If m_kind == Root */
            T *          m_elem; /* If m_kind == PushBack or m_kind == Set */
        };

        cell_kind kind() const { return static_cast<cell_kind>(m_kind); }
        unsigned idx() const { lean_assert(kind() != Root); return m_idx; }
        unsigned size() const { lean_assert(kind() == Root); return m_size; }
        cell * next() const { lean_assert(kind() != Root); return m_next; }
        T const & elem() const { lean_assert(kind() == Set || kind() == PushBack); return *m_elem; }

        mutex ** get_mutex_field_addr() {
            return reinterpret_cast<mutex**>(reinterpret_cast<char*>(this) + sizeof(cell));
        }

        mutex * get_mutex() { return *get_mutex_field_addr(); }

        void set_mutex(mutex * m) { *get_mutex_field_addr() = m; }

        cell():m_rc(1), m_kind(Root), m_size(0), m_values(nullptr) {}
    };

    static memory_pool & get_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(sizeof(cell) + (ThreadSafe ? sizeof(mutex*) : 0)); // NOLINT
        return *g_allocator;
    }

    static memory_pool & get_elem_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(std::max(sizeof(T), sizeof(size_t)));
        return *g_allocator;
    }

    static void del_elem(T * ptr) {
        ptr->~T();
        get_elem_allocator().recycle(ptr);
    }

    static void deallocate_cell(cell * c) {
        while (true) {
            cell * next = nullptr;
            switch (c->kind()) {
            case Set:
            case PushBack:
                del_elem(c->m_elem);
                next = c->next();
                break;
            case PopBack:
                next = c->next();
                break;
            case Root:
                deallocate_array(c->m_values, c->m_size);
                if (ThreadSafe)
                    delete c->get_mutex();
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

    static unsigned get_rc(cell * c) {
        if (ThreadSafe)
            return atomic_load(&c->m_rc);
        else
            return c->m_rc;
    }

    static void inc_ref(cell * c) {
        if (c == nullptr) return;
        if (ThreadSafe)
            atomic_fetch_add_explicit(&c->m_rc, 1u, memory_order_relaxed);
        else
            c->m_rc++;
    }

    static void dec_ref(cell * c) {
        if (c == nullptr) return;
        lean_assert(get_rc(c) > 0);
        if (ThreadSafe) {
            if (atomic_fetch_sub_explicit(&c->m_rc, 1u, memory_order_release) == 1u) {
                atomic_thread_fence(memory_order_acquire);
                deallocate_cell(c);
            }
        } else {
            c->m_rc--;
            if (c->m_rc == 0)
                deallocate_cell(c);
        }
    }

    static cell * mk_cell() {
        return new (get_allocator().allocate()) cell();
    }

    static T * mk_elem_copy(T const & e) {
        return new (get_elem_allocator().allocate()) T(e);
    }

    static void reroot(cell * r) {
        lean_assert(get_rc(r) > 0);
        lean_assert(r->kind() != Root);
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
                if (c->m_kind == PopBack || c->m_kind == Root) {
                    c->m_elem  = mk_elem_copy(vs[p->m_idx]);
                } else {
                    *c->m_elem = vs[p->m_idx];
                }
                c->m_kind    = Set;
                c->m_idx     = p->m_idx;
                vs[p->m_idx] = p->elem();
                break;
            case PushBack:
                if (c->m_kind == PopBack || c->m_kind == Root) {
                    c->m_elem = nullptr;
                } else {
                    del_elem(c->m_elem);
                }
                c->m_kind = PopBack;
                if (sz == capacity(vs))
                    vs = expand(vs, sz);
                c->m_idx  = sz;
                new (vs + sz) T(p->elem());
                sz++;
                break;
            case PopBack:
                --sz;
                if (c->m_kind == PopBack || c->m_kind == Root) {
                    c->m_elem  = mk_elem_copy(vs[sz]);
                } else {
                    *c->m_elem = vs[sz];
                }
                (vs + sz)->~T();
                c->m_kind = PushBack;
                c->m_idx  = sz;
                break;
            case Root:
                lean_unreachable();
                break;
            }
            c->m_next   = p;
            c = p;
        }
        lean_assert(c == r);
        if (r->m_kind == Set || r->m_kind == PushBack) {
            del_elem(r->m_elem);
        }
        r->m_kind   = Root;
        r->m_values = vs;
        r->m_size   = sz;
        inc_ref(r);
        dec_ref(last);
    }

    static cell * ensure_unshared_aux(cell * c) {
        buffer<cell *, 1024> cs;
        size_t i = 0;
        while (c->kind() != Root) {
            cs.push_back(c);
            c = c->next();
            i++;
        }
        cell * r    = mk_cell();
        r->m_rc     = 0;
        r->m_size   = c->m_size;
        r->m_values = allocate_raw_array(capacity(c->m_values));
        std::uninitialized_copy(c->m_values, c->m_values + c->m_size, r->m_values);
        i           = cs.size();
        while (i > 0) {
            --i;
            cell * p = cs[i];
            lean_assert(p->kind() != Root);
            lean_assert(p->m_next == c);
            switch (p->kind()) {
            case Set:
                r->m_values[p->m_idx] = p->elem();
                break;
            case PushBack:
                if (r->m_size == capacity(r->m_values))
                    r->m_values = expand(r->m_values, r->m_size);
                new (r->m_values + r->m_size) T(p->elem());
                r->m_size++;
                break;
            case PopBack:
                r->m_size--;
                (r->m_values + r->m_size)->~T();
                break;
            case Root:
                lean_unreachable();
                break;
            }
        }
        return r;
    }

    static cell * ensure_unshared(cell * c) {
        if (get_rc(c) == 1 && c->kind() == Root)
            return c;
        if (ThreadSafe) {
            unique_lock<mutex> lock(*c->get_mutex());
            return ensure_unshared_aux(c);
        } else {
            return ensure_unshared_aux(c);
        }
    }

    static T read_aux(cell * c, size_t i) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        lean_assert(i < c->size());
        return c->m_values[i];
    }

    static T read(cell * c, size_t i) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_assert(i < c->size());
            return c->m_values[i];
        } else if (ThreadSafe) {
            unique_lock<mutex> lock(*c->get_mutex());
            return read_aux(c, i);
        } else {
            return read_aux(c, i);
        }
    }

    static size_t size(cell * c) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            return c->size();
        } else if (ThreadSafe) {
            if (c->kind() != Root)
                reroot(c);
            return c->size();
        } else {
            if (c->kind() != Root)
                reroot(c);
            return c->size();
        }
    }

    static cell * write_aux(cell * c, size_t i, T const & v) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(i < c->size());
        if (get_rc(c) == 1) {
            c->m_values[i] = v;
            return c;
        } else {
            lean_array_trace(tout() << "non-destructive write at #" << i << "\n";);
            lean_assert(c->kind() == Root);
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            if (ThreadSafe)
                new_cell->set_mutex(c->get_mutex());
            c->m_kind             = Set;
            c->m_idx              = i;
            c->m_elem             = mk_elem_copy(new_cell->m_values[i]);
            c->m_next             = new_cell;
            /* It is safe to update m_rc directly here because
               we are protected by a semaphore */
            c->m_rc--;
            new_cell->m_rc++;
            new_cell->m_values[i] = v;
            return new_cell;
        }
    }

    static cell * write(cell * c, size_t i, T const & v) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_array_trace(tout() << "destructive write at #" << i << "\n";);
            lean_assert(i < c->size());
            c->m_values[i] = v;
            return c;
        } else if (ThreadSafe) {
            unique_lock<mutex> lock(*c->get_mutex());
            return write_aux(c, i, v);
        } else {
            return write_aux(c, i, v);
        }
    }

    static void push_back_core(cell * c, T const & v) {
        if (c->m_size == capacity(c->m_values))
            c->m_values = expand(c->m_values, c->m_size);
        new (c->m_values + c->m_size) T(v);
        c->m_size++;
    }

    static cell * push_back_aux(cell * c, T const & v) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        if (get_rc(c) == 1) {
            push_back_core(c, v);
            return c;
        }
        lean_array_trace(tout() << "non-destructive push_back\n";);
        cell * new_cell       = mk_cell();
        new_cell->m_values    = c->m_values;
        new_cell->m_size      = c->m_size;
        if (ThreadSafe)
            new_cell->set_mutex(c->get_mutex());
        c->m_kind             = PopBack;
        c->m_next             = new_cell;
        c->m_elem             = nullptr;
        /* It is safe to update m_rc directly here because
           we are protected by a semaphore */
        c->m_rc--;
        new_cell->m_rc++;
        push_back_core(new_cell, v);
        return new_cell;
    }

    static cell * push_back(cell * c, T const & v) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_array_trace(tout() << "destructive push_back\n";);
            push_back_core(c, v);
            return c;
        } else if (ThreadSafe) {
            unique_lock<mutex> lock(*c->get_mutex());
            return push_back_aux(c, v);
        } else {
            return push_back_aux(c, v);
        }
    }

    static void pop_back_core(cell * c) {
        lean_assert(c->m_size > 0);
        c->m_size--;
        c->m_values[c->m_size].~T();
    }

    static cell * pop_back_aux(cell * c) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        lean_assert(c->m_size > 0);
        if (get_rc(c) == 1) {
            pop_back_core(c);
            return c;
        } else {
            lean_array_trace(tout() << "non-destructive pop_back\n";);
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            if (ThreadSafe)
                new_cell->set_mutex(c->get_mutex());
            c->m_kind             = PushBack;
            c->m_elem             = mk_elem_copy(new_cell->m_values[c->m_size - 1]);
            c->m_next             = new_cell;
            /* It is safe to update m_rc directly here because
               we are protected by a semaphore */
            c->m_rc--;
            new_cell->m_rc++;
            pop_back_core(new_cell);
            return new_cell;
        }
    }

    static cell * pop_back(cell * c) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_assert(c->m_size > 0);
            lean_array_trace(tout() << "destructive pop_back\n";);
            pop_back_core(c);
            return c;
        } else if (ThreadSafe) {
            unique_lock<mutex> lock(*c->get_mutex());
            return pop_back_aux(c);
        } else {
            return pop_back_aux(c);
        }
    }

    void init() {
        if (ThreadSafe)
            m_cell->set_mutex(new mutex());
    }

    cell * m_cell;
public:
    parray():m_cell(mk_cell()) { init(); }
    parray(size_t sz, T const & v):m_cell(mk_cell()) {
        m_cell->m_size   = sz;
        m_cell->m_values = allocate_raw_array(sz);
        std::uninitialized_fill(m_cell->m_values, m_cell->m_values + sz, v);
        init();
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

    T operator[](size_t i) const {
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

    void ensure_unshared() {
        cell * new_cell = ensure_unshared(m_cell);
        inc_ref(new_cell);
        dec_ref(m_cell);
        m_cell = new_cell;
        lean_assert(get_rc(m_cell) == 1 && m_cell->m_kind == Root);
    }

    unsigned get_rc() const {
        return m_cell->m_rc;
    }

    static unsigned sizeof_cell() {
        return get_allocator().obj_size();
    }
};
void initialize_parray();
void finalize_parray();
}
