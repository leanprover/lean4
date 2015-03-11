/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <new>
#include <cstdlib>
#include <iostream>
#include "util/exception.h"
#include "util/memory.h"

namespace lean {
void set_max_memory_megabyte(unsigned max) {
    size_t m = max;
    m *= 1024 * 1024;
    set_max_memory(m);
}
}

#if !defined(LEAN_TRACK_MEMORY)
namespace lean {
size_t     get_allocated_memory() {
    return 0;
}

void set_max_memory(size_t) {
    throw exception("Lean was compiled without memory consumption tracking "
                    "(possible solution: compile using LEAN_TRACK_MEMORY)");
}

void check_memory(char const * component_name) {
    // do nothing when LEAN_TRACK_MEMORY is not defined
}

void * malloc(size_t sz, bool use_ex)  {
    void * r = ::malloc(sz);
    if (r || sz == 0)
        return r;
    else if (use_ex)
        throw std::bad_alloc();
    else
        return nullptr;
}

void * malloc(size_t sz) {
    return malloc(sz, true);
}

void * realloc(void * ptr, size_t sz) {
    void * r = ::realloc(ptr, sz);
    if (r || sz == 0)
        return r;
    else
        throw std::bad_alloc();
}

void free(void * ptr) {
    ::free(ptr);
}
}

#else
#include "util/thread.h"

#if defined(HAS_MALLOC_USABLE_SIZE)
#include <malloc.h> // NOLINT
namespace lean {
inline size_t malloc_size(void * ptr)             { return malloc_usable_size(ptr); }
inline void * malloc_core(size_t sz)              { return ::malloc(sz); }
inline void * realloc_core(void * ptr, size_t sz) { return ::realloc(ptr, sz); }
inline void   free_core(void * ptr)               { ::free(ptr); }
}
// REMARK: We commented the following piece of code because tc_malloc_size is hanging

// #elif defined(HAS_TCMALLOC)
// #include <gperftools/tcmalloc.h>
// namespace lean {
// inline size_t malloc_size(void * ptr)             { return tc_malloc_size(ptr); }
// inline void * malloc_core(size_t sz)              { return tc_malloc(sz); }
// inline void * realloc_core(void * ptr, size_t sz) { return tc_realloc(ptr, sz); }
// inline void   free_core(void * ptr)               { tc_free(ptr); }
// }
#elif defined(HAS_MALLOCSIZE)
#include <malloc/malloc.h> // NOLINT
namespace lean {
inline size_t malloc_size(void * ptr)             { return ::malloc_size(ptr); }
inline void * malloc_core(size_t sz)              { return ::malloc(sz); }
inline void * realloc_core(void * ptr, size_t sz) { return ::realloc(ptr, sz); }
inline void   free_core(void * ptr)               { ::free(ptr); }
}
#elif defined(HAS_MSIZE)
#include <malloc.h> // NOLINT
namespace lean {
inline size_t malloc_size(void * ptr)             { return _msize(ptr); }
inline void * malloc_core(size_t sz)              { return ::malloc(sz); }
inline void * realloc_core(void * ptr, size_t sz) { return ::realloc(ptr, sz); }
inline void   free_core(void * ptr)               { ::free(ptr); }
}
#else
namespace lean {
void * save_alloc_size(void * ptr, size_t sz) {
    if (ptr) {
        size_t * r = static_cast<size_t*>(ptr);
        *r = sz;
        return r + 1;
    } else {
        return ptr;
    }
}
inline size_t malloc_size(void * ptr)             { return static_cast<size_t*>(ptr)[-1]; }
inline void * malloc_core(size_t sz)              { return save_alloc_size(::malloc(sz + sizeof(sz)), sz); }
inline void * realloc_core(void * ptr, size_t sz) { return save_alloc_size(::realloc(static_cast<size_t*>(ptr) - 1, sz + sizeof(sz)), sz); }
inline void   free_core(void * ptr)               { ::free(static_cast<size_t*>(ptr) - 1); }
}
#endif

namespace lean {
class alloc_info {
    atomic<size_t> m_size;
public:
    alloc_info():m_size(0) {}
    ~alloc_info() {}
    void inc(size_t sz) { m_size += sz; }
    void dec(size_t sz) { m_size -= sz; }
    size_t size() const { return m_size; }
};

// TODO(Leo): use explicit initialization?
static alloc_info g_global_memory;
static size_t     g_max_memory = 0;

void set_max_memory(size_t max) {
    g_max_memory = max;
}

size_t get_allocated_memory() {
    return g_global_memory.size();
}

void check_memory(char const * component_name) {
    if (g_max_memory != 0 && get_allocated_memory() > g_max_memory)
        throw memory_exception(component_name);
}

void * malloc(size_t sz, bool use_ex)  {
    void * r = malloc_core(sz);
    if (r || sz == 0) {
        size_t rsz = malloc_size(r);
        g_global_memory.inc(rsz);
        return r;
    } else if (use_ex) {
        throw std::bad_alloc();
    } else {
        return nullptr;
    }
}

void * malloc(size_t sz) {
    return malloc(sz, true);
}

void * realloc(void * ptr, size_t sz) {
    if (ptr == nullptr)
        return malloc(sz);
    if (sz == 0) {
        free(ptr);
        return nullptr;
    }
    size_t old_sz = malloc_size(ptr);
    g_global_memory.dec(old_sz);
    void * r = realloc_core(ptr, sz);
    size_t new_sz = malloc_size(r);
    g_global_memory.inc(new_sz);
    if (r || sz == 0)
        return r;
    else
        throw std::bad_alloc();
}

void free(void * ptr) {
    if (ptr) {
        size_t sz = malloc_size(ptr);
        g_global_memory.dec(sz);
    }
    free_core(ptr);
}
}

void* operator new(std::size_t sz) throw(std::bad_alloc) { return lean::malloc(sz, true); }
void  operator delete(void * ptr) throw() { return lean::free(ptr); }
void* operator new[](std::size_t sz) throw(std::bad_alloc) { return lean::malloc(sz, true); }
void  operator delete[](void * ptr) throw() { return lean::free(ptr); }
void* operator new(std::size_t sz, std::nothrow_t const &) noexcept { return lean::malloc(sz, false); }
void* operator new[](std::size_t sz, std::nothrow_t const &) noexcept { return lean::malloc(sz, false); }
#endif
