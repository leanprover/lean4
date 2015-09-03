/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <thread>
#include <iostream>
#include "api/lean.h"

void check_core(int v, unsigned l) {
    if (!v) {
        printf("Test failed at line %d\n", l);
        exit(1);
    }
}

#define check(v) check_core(v, __LINE__)

lean_name mk_name(char const * n) {
    lean_exception ex;
    lean_name a, r;
    check(lean_name_mk_anonymous(&a, &ex));
    check(lean_name_mk_str(a, n, &r, &ex));
    lean_name_del(a);
    return r;
}

lean_list_name mk_unary_name_list(lean_name u) {
    lean_exception ex;
    lean_list_name n, r;
    check(lean_list_name_mk_nil(&n, &ex));
    check(lean_list_name_mk_cons(u, n, &r, &ex));
    lean_list_name_del(n);
    return r;
}

lean_env mk_env() {
    lean_exception ex;
    lean_env r;
    check(lean_env_mk_std(LEAN_TRUST_HIGH, &r, &ex));
    return r;
}

void test_import() {
    lean_exception ex;
    lean_env  env     = mk_env();
    lean_name std     = mk_name("standard");
    lean_list_name ms = mk_unary_name_list(std);
    lean_options o;
    lean_ios ios;
    lean_env new_env;
    check(lean_options_mk_empty(&o, &ex));
    check(lean_ios_mk_std(o, &ios, &ex));
    check(lean_env_import(env, ios, ms, &new_env, &ex));
    lean_env_del(env);
    lean_env_del(new_env);
    lean_name_del(std);
    lean_list_name_del(ms);
    lean_options_del(o);
    lean_ios_del(ios);
}

int main() {
    std::thread t1(test_import);
    std::thread t2(test_import);
    t1.join();
    t2.join();
    return 0;
}
