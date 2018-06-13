/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include <sstream>
#include "util/test.h"
#include "util/nat.h"
#include "util/init_module.h"
using namespace lean;

static void tst1() {
    lean_assert(nat("10000000000000000000") + nat("10000000000000000000") == nat("20000000000000000000"));
    lean_assert(nat(1) == nat(2) - nat(1));
    lean_assert(nat(30) * nat(10) == nat(300));
    lean_assert(nat(7) / nat(2) == nat(3));
    lean_assert(nat(11) % nat(3) == nat(2));
    lean_assert(nat("-10") == nat(0));
    lean_assert(nat(-1) == nat(0));
    nat v(10);
    v = v + nat(1);
    lean_assert(v == nat(11));
    lean_assert(nat(12) != nat("11"));
    lean_assert(nat(10) < nat(100));
    lean_assert(nat(10) <= nat(100));
    lean_assert(nat(10) <= nat(10));
    lean_assert(!(nat(10) < nat(10)));
    lean_assert(!(nat(11) < nat(10)));
    lean_assert(!(nat(10) > nat(100)));
    lean_assert(!(nat(10) >= nat(100)));
    lean_assert(nat(10) >= nat(10));
    lean_assert(!(nat(10) > nat(10)));
    lean_assert(nat(11) > nat(10));
    lean_assert(nat(20) > nat(10));
    lean_assert(nat(20) >= nat(10));
    lean_assert(nat(20).is_small());
    lean_assert(nat(1).get_small_value() == 1);
    lean_assert(!nat("10000000000000000000").is_small());
    lean_assert(nat("10000000000000000000").get_big_value() == mpz("10000000000000000000"));
    lean_assert(nat(1).to_mpz() == mpz(1));
    lean_assert(nat("10000000000000000000").to_mpz() == mpz("10000000000000000000"));
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
