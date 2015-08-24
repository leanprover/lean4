/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <pthread.h>
#include <memory.h>
#include <iostream>
#include "util/thread.h"
#include "util/exception.h"

#if !defined(LEAN_USE_SPLIT_STACK)

#if defined(LEAN_WINDOWS)
    // no extra included needed so far
#elif defined(__APPLE__)
    #include <sys/resource.h> // NOLINT
#else
    #include <sys/time.h> // NOLINT
    #include <sys/resource.h> // NOLINT
#endif

#define LEAN_MIN_STACK_SPACE 128*1024  // 128 Kb

namespace lean {
void throw_get_stack_size_failed() {
    throw exception("failed to retrieve thread stack size");
}

#if defined(LEAN_WINDOWS)
size_t get_stack_size(int ) {
    return LEAN_WIN_STACK_SIZE;
}
#elif defined (__APPLE__)
size_t get_stack_size(int main) {
    if (main) {
        // Retrieve stack size of the main thread.
        struct rlimit curr;
        if (getrlimit(RLIMIT_STACK, &curr) != 0) {
            throw_get_stack_size_failed();
        }
        return curr.rlim_cur;
    } else {
        #if defined(LEAN_MULTI_THREAD)
        {
            #if defined(LEAN_USE_BOOST)
            // Boost does seems to be based on pthread on OSX
            return get_thread_attributes().get_stack_size();
            #else
            // This branch retrieves the default thread size for pthread threads.
            // This is *not* the stack size of the main thread.
            pthread_attr_t attr;
            memset (&attr, 0, sizeof(attr));
            pthread_attr_init(&attr);
            size_t result;
            if (pthread_attr_getstacksize(&attr, &result) != 0) {
                throw_get_stack_size_failed();
            }
            return result;
            #endif
        }
        #else
        return 0;
        #endif
    }
}
#else
size_t get_stack_size(int main) {
    if (main) {
        // Retrieve stack size of the main thread.
        struct rlimit curr;
        if (getrlimit(RLIMIT_STACK, &curr) != 0) {
            throw_get_stack_size_failed();
        }
        return curr.rlim_cur;
    } else {
        #if defined(LEAN_MULTI_THREAD)
        pthread_attr_t attr;
        memset (&attr, 0, sizeof(attr));
        if (pthread_getattr_np(pthread_self(), &attr) != 0) {
            throw_get_stack_size_failed();
        }
        void * ptr;
        size_t result;
        if (pthread_attr_getstack (&attr, &ptr, &result) != 0) {
            throw_get_stack_size_failed();
        }
        if (pthread_attr_destroy(&attr) != 0) {
            throw_get_stack_size_failed();
        }
        return result;
        #else
        return 0;
        #endif
    }
}
#endif

LEAN_THREAD_VALUE(bool, g_stack_info_init, false);
LEAN_THREAD_VALUE(size_t, g_stack_size, 0);
LEAN_THREAD_VALUE(size_t, g_stack_base, 0);

void save_stack_info(bool main) {
    g_stack_info_init = true;
    g_stack_size = get_stack_size(main);
    char x;
    g_stack_base = reinterpret_cast<size_t>(&x);
}

size_t get_used_stack_size() {
    char y;
    size_t curr_stack = reinterpret_cast<size_t>(&y);
    return g_stack_base - curr_stack;
}

size_t get_available_stack_size() {
    size_t sz = get_used_stack_size();
    if (sz > g_stack_size)
        return 0;
    else
        return g_stack_size - sz;
}

void check_stack(char const * component_name) {
    if (!g_stack_info_init)
        save_stack_info(false);
    if (get_used_stack_size() + LEAN_MIN_STACK_SPACE > g_stack_size)
        throw stack_space_exception(component_name);
}
}
#endif
