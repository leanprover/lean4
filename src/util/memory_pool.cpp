/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/thread.h"
#include "util/memory_pool.h"

namespace lean {
memory_pool::~memory_pool() {
    while (m_free_list != nullptr) {
        void * r = m_free_list;
        m_free_list = *(reinterpret_cast<void **>(r));
        free(r);
    }
}

void * memory_pool::allocate() {
    if (m_free_list != nullptr) {
        void * r = m_free_list;
        m_free_list = *(reinterpret_cast<void **>(r));
        return r;
    } else {
        return malloc(m_size);
    }
}

typedef std::vector<memory_pool*> memory_pools;
LEAN_THREAD_PTR(memory_pools, g_thread_pools);

static void thread_finalize_memory_pool(void * p) {
    std::vector<memory_pool*> * thread_pools = reinterpret_cast<std::vector<memory_pool*>*>(p);
    unsigned i = thread_pools->size();
    while (i > 0) {
        --i;
        delete (*thread_pools)[i];
    }
    delete thread_pools;
    g_thread_pools = nullptr;
}

memory_pool * allocate_thread_memory_pool(unsigned sz) {
    if (!g_thread_pools) {
        g_thread_pools = new std::vector<memory_pool*>();
        register_post_thread_finalizer(thread_finalize_memory_pool, g_thread_pools);
    }
    memory_pool * r = new memory_pool(sz);
    g_thread_pools->push_back(r);
    return r;
}
}
