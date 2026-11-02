/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <cstdlib>
#include <cstring>
#include "runtime/compact.h"

// The linker wraps malloc in the runtime sources, without changing allocations
// inside libc or libstdc++. Each failing case runs in a separate process.
static bool fail_next_malloc = false;

extern "C" void * __real_malloc(size_t size);

extern "C" void * __wrap_malloc(size_t size) {
    if (fail_next_malloc) {
        fail_next_malloc = false;
        return nullptr;
    }
    return __real_malloc(size);
}

int main(int argc, char ** argv) {
    if (argc != 2) return 2;
    bool initial = std::strcmp(argv[1], "initial") == 0;
    bool growth = std::strcmp(argv[1], "growth") == 0;
    bool control = std::strcmp(argv[1], "control") == 0;
    if (!initial && !growth && !control) return 2;

    fail_next_malloc = initial;
    lean::object_compactor compactor;
    // Fill the initial 1 MiB buffer, then require it to grow. The successful
    // control checks that growth preserves its contents and zeroes new bytes.
    constexpr size_t initial_size = 1024 * 1024;
    void * first = compactor.alloc(initial_size);
    std::memset(first, 0x5a, initial_size);
    fail_next_malloc = growth;
    auto * added = static_cast<unsigned char *>(compactor.alloc(sizeof(void *)));
    if (!control) return 2; // Allocation failure must take the OOM panic path.
    if (compactor.size() != initial_size + sizeof(void *)) return 1;
    auto * data = static_cast<unsigned char const *>(compactor.data());
    for (size_t i = 0; i < initial_size; ++i)
        if (data[i] != 0x5a) return 1;
    for (size_t i = 0; i < sizeof(void *); ++i)
        if (added[i] != 0) return 1;
    return 0;
}
