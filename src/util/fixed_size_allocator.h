/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/memory.h"

namespace lean {
template<unsigned Size>
class fixed_size_allocator {
    void * m_free_list;
public:
    fixed_size_allocator():m_free_list(nullptr) {}
    ~fixed_size_allocator() {
        while (m_free_list != nullptr) {
            void * r = m_free_list;
            m_free_list = *(reinterpret_cast<void **>(r));
            free(r);
        }
    }

    void * allocate() {
        if (m_free_list != nullptr) {
            void * r = m_free_list;
            m_free_list = *(reinterpret_cast<void **>(r));
            return r;
        } else {
            return malloc(Size);
        }
    }

    void recyle(void * ptr) {
        *(reinterpret_cast<void**>(ptr)) = m_free_list;
        m_free_list = ptr;
    }
};
}
