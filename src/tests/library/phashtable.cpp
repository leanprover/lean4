/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <random>
#include <vector>
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/phashtable.h"
using namespace lean;

typedef phashtable<unsigned, std::hash<unsigned>, std::equal_to<unsigned>, true> unsigned_set;

void tst1() {
    unsigned_set s;
    lean_assert(s.size() == 0);
    s.insert(10);
    s.for_each([](unsigned v) {
            lean_assert(v == 10);
        });
    lean_assert(s.contains(10));
    lean_assert(!s.contains(20));
    lean_assert(s.find(10));
    auto v = s.find(10);
    lean_assert(v && *v == 10);
    lean_assert(!s.find(20));
    s.erase(20);
    lean_assert(s.check_invariant());
    lean_assert(s.contains(10));
    s.erase(10);
    lean_assert(!s.contains(10));
    lean_assert(s.check_invariant());
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_core_module();
    initialize_library_module();

    tst1();

    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
