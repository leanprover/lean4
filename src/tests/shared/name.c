/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <stdlib.h>
#include <stdio.h>
#include "api/lean.h"

void check_core(int v, unsigned l) {
    if (!v) {
        printf("Test failed at line %d\n", l);
        exit(1);
    }
}

#define check(v) check_core(v, __LINE__)

void anonymous_unique() {
    lean_exception ex;
    lean_name a1, a2;
    check(lean_name_mk_anonymous(&a1, &ex));
    check(lean_name_mk_anonymous(&a2, &ex));
    check(lean_name_eq(a1, a2));
    lean_name_del(a1);
    lean_name_del(a2);
}

int main() {
    lean_exception ex;
    lean_name a, n1, n2, n3, n4, n5, n6;
    char const * s1;
    char const * s2;
    char const * s3;
    lean_list_name l1, l2, l3, l4;
    unsigned idx;
    printf("Started name test\n");
    check(lean_name_mk_anonymous(&a, &ex));
    check(lean_name_is_anonymous(a));
    check(lean_name_mk_str(a, "foo", &n1, &ex));
    check(lean_name_mk_str(n1, "bla", &n2, &ex));
    check(lean_name_to_string(n2, &s1, &ex));
    printf("Lean name: %s\n", s1);
    check(lean_name_is_str(n2));
    check(!lean_name_is_anonymous(n2));
    check(!lean_name_is_idx(n2));
    check(lean_name_mk_idx(n2, 1, &n3, &ex));
    check(lean_name_to_string(n3, &s2, &ex));
    printf("Lean name: %s\n", s2);
    check(lean_name_is_idx(n3));
    check(lean_name_get_prefix(n3, &n4, &ex));
    check(lean_name_eq(n2, n4));
    check(lean_name_get_idx(n3, &idx, &ex));
    check(idx == 1);
    check(!lean_name_get_prefix(a, &n5, &ex));
    s3 = lean_exception_get_message(ex);
    printf("Lean exception: %s\n", s3);

    check(lean_list_name_mk_nil(&l1, &ex));
    check(!lean_list_name_is_cons(l1));
    check(lean_list_name_mk_cons(n1, l1, &l2, &ex));
    check(lean_list_name_is_cons(l2));
    check(lean_list_name_mk_cons(n2, l2, &l3, &ex));
    check(lean_list_name_head(l3, &n6, &ex));
    check(lean_name_eq(n6, n2));
    check(lean_list_name_tail(l3, &l4, &ex));
    check(lean_list_name_eq(l4, l2));

    anonymous_unique();
    lean_name_del(a);
    lean_name_del(n1);
    lean_name_del(n2);
    lean_name_del(n3);
    lean_name_del(n4);
    lean_name_del(n6);
    lean_list_name_del(l1);
    lean_list_name_del(l2);
    lean_list_name_del(l3);
    lean_list_name_del(l4);
    lean_string_del(s1);
    lean_string_del(s2);
    lean_string_del(s3);
    lean_exception_del(ex);
    return 0;
}
