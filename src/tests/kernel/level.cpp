/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <locale>
#include "util/test.h"
#include "util/exception.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "kernel/level.h"
#include "library/kernel_serializer.h"
#include "library/init_module.h"
using namespace lean;

static void check_serializer(level const & l) {
    std::ostringstream out;
    serializer s(out);
    s << l << l;
    std::istringstream in(out.str());
    deserializer d(in);
    level l1, l2;
    d >> l1 >> l2;
    lean_assert_eq(l, l1);
    lean_assert_eq(l, l2);
}

static void tst1() {
    level zero;
    level one = mk_succ(zero);
    level two = mk_succ(one);
    lean_assert(mk_max(one, two) == two);
    lean_assert(mk_imax(one, two) == two);
    lean_assert(mk_imax(two, zero) == zero);
    check_serializer(two);
    check_serializer(one);
    level p = mk_param_univ("p");
    lean_assert(mk_imax(p, zero) == zero);
    lean_assert(mk_max(zero, p) == p);
    lean_assert(mk_max(p, zero) == p);
    lean_assert(mk_max(p, one) != p);
    check_serializer(mk_max(p, one));
    check_serializer(mk_imax(p, one));
    check_serializer(mk_imax(one, p));
    check_serializer(mk_imax(mk_succ(p), p));
    std::cout << pp(mk_max(p, mk_max(mk_succ(mk_param_univ("a")), one))) << "\n";
}

static void tst2() {
    level zero;
    level one = mk_succ(zero);
    level two = mk_succ(one);
    level p1 = mk_param_univ("p1");
    level p2 = mk_param_univ("p2");
    level m1 = mk_meta_univ("m1");
    lean_assert(is_equivalent(mk_succ(p2), mk_max(p2, mk_succ(p2))));
    lean_assert(is_equivalent(mk_max(p1, p2), mk_max(p2, p1)));
    lean_assert(!is_equivalent(mk_imax(p1, p2), mk_imax(p2, p1)));
    lean_assert(is_equivalent(mk_imax(mk_succ(p1), mk_succ(p2)), mk_imax(mk_succ(p2), mk_succ(p1))));
    lean_assert(is_equivalent(mk_succ(mk_max(m1, p1)), mk_max(mk_succ(p1), mk_succ(m1))));
    lean_assert(is_equivalent(one, mk_succ(zero)));
    lean_assert(!is_equivalent(zero, two));
    lean_assert(!is_equivalent(zero, p2));
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_module();
    tst1();
    tst2();
    finalize_library_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
