/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "util/memory.h"

static void tst1() {
    std::cout << "Initial: " << lean::get_allocated_memory() << "\n";
    size_t old_mem = lean::get_allocated_memory();
    int N = 5;
    int * a = static_cast<int*>(lean::malloc(N * sizeof(N)));
    lean_assert(lean::get_allocated_memory() >= old_mem + N * sizeof(N));
    for (int i = 0; i < N; i++) {
        a[i] = i;
    }
    a = static_cast<int*>(lean::realloc(a, N * 2 * sizeof(N)));
    lean_assert(lean::get_allocated_memory() >= old_mem + N * 2 * sizeof(N));
    std::cout << "Total: "  << static_cast<size_t>(lean::get_allocated_memory()) << "\n";
    for (int i = 0; i < N; i++) {
        lean_assert(a[i] == i);
    }
    lean::free(a);
    lean_assert_eq(old_mem, lean::get_allocated_memory());
}

int main() {
    tst1();
    return lean::has_violations() ? 1 : 0;
}
