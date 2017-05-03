/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/memory.h"

#define LEAN_FREE_LIST_MAX_SIZE 8192

namespace lean {
/** \brief Auxiliary object for "recycling" allocated memory of fixed size */
class memory_pool {
    unsigned m_size;
    unsigned m_free_list_size;
    void *   m_free_list;
public:
    memory_pool(unsigned size):m_size(size), m_free_list_size(0), m_free_list(nullptr) {}
    ~memory_pool();
    void * allocate();
    void recycle(void * ptr) {
#ifdef LEAN_NO_CUSTOM_ALLOCATORS
        free(ptr);
#else
        if (m_free_list_size > LEAN_FREE_LIST_MAX_SIZE) {
            free(ptr);
        } else {
            *(reinterpret_cast<void**>(ptr)) = m_free_list;
            m_free_list = ptr;
            m_free_list_size++;
        }
#endif
    }
    unsigned obj_size() const { return m_size; }
};

memory_pool * allocate_thread_memory_pool(unsigned sz);

#define DEF_THREAD_MEMORY_POOL(NAME, SZ)                        \
LEAN_THREAD_PTR(memory_pool, NAME ## _tlocal);                  \
memory_pool & NAME() {                                          \
    if (!NAME ## _tlocal)                                       \
        NAME ## _tlocal = allocate_thread_memory_pool(SZ);      \
    return *(NAME ## _tlocal);                                  \
}
}
