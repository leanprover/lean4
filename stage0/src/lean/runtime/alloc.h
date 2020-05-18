/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstddef>

namespace lean {
void init_thread_heap();
void * alloc(size_t sz);
void dealloc(void * o, size_t sz);
void initialize_alloc();
void finalize_alloc();
}
