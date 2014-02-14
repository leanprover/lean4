/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <locale>
#include "util/test.h"
#include "util/exception.h"
#include "kernel/level.h"
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
    level p = mk_param_univ(0);
    lean_assert(mk_imax(p, zero) == zero);
    lean_assert(mk_max(zero, p) == p);
    lean_assert(mk_max(p, zero) == p);
    lean_assert(mk_max(p, one) != p);
    check_serializer(mk_max(p, one));
    check_serializer(mk_imax(p, one));
    check_serializer(mk_imax(one, p));
    check_serializer(mk_imax(mk_succ(p), p));
    std::cout << pp(mk_max(p, mk_max(mk_succ(mk_param_univ(1)), one))) << "\n";
}


#if 0
static void tst0() {
    environment env;
    lean_assert(env->begin_objects() == env->end_objects());
    std::for_each(env->begin_objects(), env->end_objects(), [&](object const & obj) {
            std::cout << obj.keyword() << "\n";
        });
    level l1 = env->add_uvar_cnstr(name(name("l1"), "suffix"), level());
    lean_assert(env->begin_objects() != env->end_objects());
    std::for_each(env->begin_objects(), env->end_objects(), [&](object const & obj) {
            std::cout << obj.keyword() << "\n";
        });
    std::cout << env;
}

static void tst1() {
    environment env;
    level l1 = env->add_uvar_cnstr(name(name("l1"), "suffix"), level());
    level l2 = env->add_uvar_cnstr("l2", l1 + 10);
    level l3 = env->add_uvar_cnstr("l3", max(l2, l1 + 3));
    level l4 = env->add_uvar_cnstr("l4", max(l1 + 8, max(l2 + 2, l3 + 20)));
    check_serializer(l1);
    check_serializer(l2);
    check_serializer(l3);
    check_serializer(l4);
    std::cout << pp(max(l1 + 8, max(l2 + 2, l3 + 20))) << "\n";
    std::cout << pp(level()) << "\n";
    std::cout << pp(level()+1) << "\n";
    std::cout << env;
    lean_assert(env->is_ge(l4 + 10, l3 + 30));
    lean_assert(!env->is_ge(l4 + 9, l3 + 30));
}

static void tst2() {
    environment env;
    level l1 = env->add_uvar_cnstr("l1", level());
    level l2 = env->add_uvar_cnstr("l1", level());
}

static void tst3() {
    environment env;
    level l1 = env->add_uvar_cnstr("l1", level());
    level l2 = env->add_uvar_cnstr("l2", l1 + ((1<<30) + 1024));
    check_serializer(l2);
    try {
        level l3 = env->add_uvar_cnstr("l3", l2 + (1<<30));
        lean_unreachable();
    }
    catch (exception & ex) {
        std::cout << "ok\n";
    }
}

static void tst4() {
    environment env;
    level l1 = env->add_uvar_cnstr("l1", level() + 1);
    level l2 = env->add_uvar_cnstr("l2", level() + 1);
    level l3 = env->add_uvar_cnstr("l3", max(l1, l2) + 1);
    level l4 = env->add_uvar_cnstr("l4", l3 + 1);
    level l5 = env->add_uvar_cnstr("l5", l3 + 1);
    level l6 = env->add_uvar_cnstr("l6", max(l4, l5) + 1);
    check_serializer(l1);
    check_serializer(l2);
    check_serializer(l3);
    check_serializer(l4);
    check_serializer(l5);
    check_serializer(l6);
    lean_assert(!env->is_ge(l5 + 1, l6));
    lean_assert(env->is_ge(l6, l5));
    lean_assert(env->is_ge(l6, max({l1, l2, l3, l4, l5})));
    lean_assert(env->is_ge(l6, l6));
    lean_assert(!env->is_ge(l5, l4));
    lean_assert(env->is_ge(max({l1, l2, l4, l5}), max({l1, l2, l3, l4, l5})));
    lean_assert(env->is_ge(max({l4, l5}), max({l1, l2, l3})));
    lean_assert(!env->is_ge(max({l1, l2, l5}), max({l1, l2, l3, l4, l5})));
    lean_assert(!env->is_ge(max({l2, l4}), max({l1, l2, l3, l4, l5})));
    lean_assert(env->is_ge(max(l2, l3) + 1, max(l1, l1+1)));
    lean_assert(env->is_ge(max(l2, l3) + 1, max(l1+2, l1+1)));
    lean_assert(env->is_ge(max(l2, l3) + 1, max(l2+2, l1+1)));
    lean_assert(!env->is_ge(max(l4, l5) + 1, max(l2+4, l1+1)));
    lean_assert(!env->is_ge(max(l6, l5), max(l2+4, l1+1)));
    lean_assert(env->is_ge(max(l6, l5), max(l2+3, l1+1)));
    lean_assert(!env->is_ge(max(l6, l5), max(l2, l1+1)+3));
    lean_assert(env->is_ge(max(l6+1, l5), max(l2, l1+1)+3));
    std::cout << env;
}

static void tst5() {
    environment env;
    level l1 = env->add_uvar_cnstr("l1", level() + 1);
    level l2 = env->add_uvar_cnstr("l2", level() + 1);
    std::cout << max(l1, l1) << "\n";
    lean_assert(max(l1, l1) == l1);
    lean_assert(max(l1+1, l1+1) == l1+1);
    std::cout << max(l1, l1+1) << "\n";
    std::cout << max(l2, max(l1, l1+1)) << "\n";
    lean_assert(max(l1, l1+1) == l1+1);
    lean_assert(max(l2, max(l1, l1+1)) == max(l2, l1+1));
    std::cout << max(l1, max(l2, l1+1)) << "\n";
    lean_assert(max(l1, max(l2, l1+1)) == max(l1+1, l2));
}
#endif

int main() {
    save_stack_info();
    tst1();
#if 0
    tst0();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
#endif
    return has_violations() ? 1 : 0;
}
