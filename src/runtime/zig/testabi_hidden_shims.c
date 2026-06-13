// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

#include <stdlib.h>

/* The Zig allocator frees legacy small objects through mimalloc, which is
 * statically linked into Lean binaries but not shipped as a standalone
 * archive. Provide weak malloc-backed stubs so every consumer of the
 * testabi archive links without mimalloc; binaries that link the real
 * runtime override them. */
__attribute__((weak)) void *mi_malloc(size_t size) {
    return malloc(size);
}

__attribute__((weak)) void mi_free(void *ptr) {
    free(ptr);
}

__attribute__((weak)) void mi_free_size(void *ptr, size_t size) {
    (void)size;
    free(ptr);
}

__attribute__((weak)) void *leanrt_cpp_partial_hidden_current_task_swap(void *task) {
    return task;
}

__attribute__((weak)) void leanrt_cpp_partial_hidden_reset_heartbeat(void) {}

__attribute__((weak)) void leanrt_cpp_partial_hidden_lean_inc_heartbeat_impl(void) {}

__attribute__((weak)) void *leanrt_cpp_partial_hidden_cancel_tk_get(void) {
    return 0;
}

__attribute__((weak)) void *leanrt_cpp_partial_hidden_cancel_tk_swap(void *token) {
    return token;
}
