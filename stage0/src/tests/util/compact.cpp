/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "runtime/serializer.h"
#include "runtime/sstream.h"
#include "runtime/compact.h"
#include "util/object_ref.h"
#include "util/name.h"
#include "util/init_module.h"
using namespace lean;

void tst1() {
    object_compactor c;
    name n1{"hello", "bla", "world", "foo", "boo"};
    c(n1.raw());
    c(n1.raw());
    mpz v("1000000000000000000000000000000");
    object_ref m(mk_nat_obj(v));
    c(m.raw());
    c(object_ref(mk_nat_obj(mpz("2000000000000000000000000000"))).raw());
    std::cout << "size: " << c.size() << "\n";
    compacted_region r(c);
    name n2(r.read());
    name n3(r.read());
    std::cout << n2 << "\n";
    lean_assert(n1.raw() != n2.raw());
    lean_assert(n2.raw() == n3.raw());
    object_ref m2(r.read());
    inc(m2.raw());
    std::cout << mpz_value(m2.raw()) << "\n";
    lean_assert(mpz_value(m2.raw()) == mpz_value(m.raw()));
    std::cout << mpz_value(r.read()) << "\n";
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
