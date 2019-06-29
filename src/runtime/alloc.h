/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstddef>
#include "runtime/thread.h"
#include "runtime/debug.h"

#define LEAN_OBJECT_SIZE_DELTA     8
#define LEAN_MAX_SMALL_OBJECT_SIZE 512
#define LEAN_PAGE_SIZE             8192        // 8 Kb

namespace lean {
namespace allocator {
struct heap;
struct page;
struct page_header {
    atomic<heap *>   m_heap;
    page *           m_next;
    page *           m_prev;
    void *           m_free_list;
    unsigned         m_max_free;
    unsigned         m_num_free;
    unsigned         m_slot_idx;
    bool             m_in_page_free_list;
};

struct page {
    page_header m_header;
    char        m_data[LEAN_PAGE_SIZE - sizeof(page_header)];
    page * get_next() const { return m_header.m_next; }
    page * get_prev() const { return m_header.m_prev; }
    void set_next(page * n) { m_header.m_next = n; }
    void set_prev(page * p) { m_header.m_prev = p; }
    void set_heap(heap * h) { m_header.m_heap = h; }
    heap * get_heap() { return m_header.m_heap; }
    bool has_many_free() const { return m_header.m_num_free > m_header.m_max_free / 4; }
    bool in_page_free_list() const { return m_header.m_in_page_free_list; }
    unsigned get_slot_idx() const { return m_header.m_slot_idx; }
    void push_free_obj(void * o);
};

LEAN_THREAD_EXTERN_PTR(page *, g_curr_pages);

inline size_t align(size_t v, size_t a) {
    return (v / a)*a + a * (v % a != 0);
}

inline char * align_ptr(char * p, size_t a) {
    return reinterpret_cast<char*>(align(reinterpret_cast<size_t>(p), a));
}

inline unsigned get_slot_idx(unsigned obj_size) {
    lean_assert(obj_size > 0);
    lean_assert(align(obj_size, LEAN_OBJECT_SIZE_DELTA) == obj_size);
    return obj_size / LEAN_OBJECT_SIZE_DELTA - 1;
}

inline void set_next_obj(void * obj, void * next) {
    *reinterpret_cast<void**>(obj) = next;
}

inline void * get_next_obj(void * obj) {
    return *reinterpret_cast<void**>(obj);
}

}

void init_thread_heap();
void * alloc(size_t sz);
void dealloc(void * o, size_t sz);
#ifndef LEAN_RUNTIME_STATS
void * alloc_small_slow(size_t sz, unsigned slot_idx);
void * big_alloc(size_t sz);
/* This function is useful when we statically know the size `sz`.
   In this case, the compiler can statically simplify some of the checks. */
inline void * alloc_small(size_t sz) {
    sz = allocator::align(sz, LEAN_OBJECT_SIZE_DELTA);
    if (sz <= LEAN_MAX_SMALL_OBJECT_SIZE) {
        lean_assert(allocator::g_curr_pages);
        unsigned slot_idx = allocator::get_slot_idx(sz);
        allocator::page * p = allocator::g_curr_pages[slot_idx];
        void * r = p->m_header.m_free_list;
        if (r != nullptr) {
            p->m_header.m_free_list = allocator::get_next_obj(r);
            p->m_header.m_num_free--;
            return r;
        }
        return alloc_small_slow(sz, slot_idx);
    } else {
        return big_alloc(sz);
    }
}
#else
/* When LEAN_RUNTIME_STATS is enabled, we collect allocation statistics.
   We just use the vanilla `alloc` in this case. */
inline void * alloc_small(size_t sz) { return alloc(sz); }
#endif

void initialize_alloc();
void finalize_alloc();
}
