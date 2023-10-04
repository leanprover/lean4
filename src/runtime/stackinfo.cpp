/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory.h>
#include <iostream>
#include "runtime/thread.h"
#include "runtime/exception.h"

#if !defined(LEAN_USE_SPLIT_STACK)
#if defined(LEAN_WINDOWS)
    // no extra included needed so far
#elif defined(__APPLE__)
    #include <sys/resource.h> // NOLINT
#else
    #include <sys/time.h> // NOLINT
    #include <sys/resource.h> // NOLINT
#endif

#if defined(LEAN_EMSCRIPTEN)
#include <emscripten/stack.h>
#endif

namespace lean {
void throw_get_stack_size_failed() {
    throw exception("failed to retrieve thread stack size");
}

#if defined(LEAN_WINDOWS)
size_t get_stack_size(int main) {
    if (main) {
        return LEAN_WIN_STACK_SIZE;
    } else {
        return lthread::get_thread_stack_size();
    }
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
        return lthread::get_thread_stack_size();
    }
}
#elif defined(LEAN_EMSCRIPTEN)
size_t get_stack_size(int main) {
    if (main) {
        return emscripten_stack_get_end() - emscripten_stack_get_base();
    } else {
        return lthread::get_thread_stack_size();
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
        return lthread::get_thread_stack_size();
    }
}
#endif

LEAN_THREAD_VALUE(bool, g_stack_info_init, false);
LEAN_THREAD_VALUE(size_t, g_stack_size, 0);
LEAN_THREAD_VALUE(size_t, g_stack_base, 0);
LEAN_THREAD_VALUE(size_t, g_stack_threshold, 0);

void save_stack_info(bool main) {
    g_stack_info_init = true;
    g_stack_size = get_stack_size(main);
    char x;
    g_stack_base = reinterpret_cast<size_t>(&x);
    /* g_stack_threshold is a redundant value used to optimize check_stack */
    g_stack_threshold = g_stack_base + LEAN_STACK_BUFFER_SPACE - g_stack_size;
    if (g_stack_threshold > g_stack_base + LEAN_STACK_BUFFER_SPACE) {
        // negative overflow
        g_stack_threshold = 0;
    }
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

// separate definition to allow breakpoint in debugger
void throw_stack_space_exception(char const * component_name) {
    throw stack_space_exception(component_name);
}

void check_stack(char const * component_name) {
    if (!g_stack_info_init)
        save_stack_info(false);
    char y;
    size_t curr_stack = reinterpret_cast<size_t>(&y);
    if (curr_stack < g_stack_threshold)
        throw_stack_space_exception(component_name);
}
}
#endif
