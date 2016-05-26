/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/debug.h"

namespace lean {
class small_object_allocator {
    static const unsigned PTR_ALIGNMENT  = (sizeof(unsigned) == sizeof(void*) ? 2 /* 32 bit */ : 3 /* 64 bit */); // NOLINT
    static const unsigned CHUNK_SIZE     = (8192 - sizeof(void*)*2); // NOLINT
    static const unsigned SMALL_OBJ_SIZE = 256;
    static const unsigned NUM_SLOTS      = (SMALL_OBJ_SIZE >> PTR_ALIGNMENT);
    static const unsigned MASK           = ((1 << PTR_ALIGNMENT) - 1);
    struct chunk {
        chunk * m_next;
        char  * m_curr;
        char    m_data[CHUNK_SIZE];
        chunk():m_curr(m_data) {}
    };
    chunk *      m_chunks[NUM_SLOTS];
    void  *      m_free_list[NUM_SLOTS];
    size_t       m_alloc_size;
    char const * m_id;
public:
    small_object_allocator(char const * id = "unknown");
    ~small_object_allocator();
    void reset();
    void * allocate(size_t size);
    void deallocate(size_t size, void * p);
    size_t get_allocation_size() const { return m_alloc_size; }
    size_t get_wasted_size() const;
    size_t get_num_free_objs() const;
    void consolidate();
};
}

inline void * operator new(size_t s, lean::small_object_allocator & r) { return r.allocate(s); }
inline void * operator new[](size_t s, lean::small_object_allocator & r) { return r.allocate(s); }
inline void operator delete(void *, lean::small_object_allocator &) { lean_unreachable(); }
inline void operator delete[](void *, lean::small_object_allocator &) { lean_unreachable(); }
