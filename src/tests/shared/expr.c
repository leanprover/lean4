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

void test_var() {
    lean_exception ex;
    lean_expr e1, e2, e3;
    lean_bool b; unsigned i;
    check(lean_expr_mk_var(0, &e1, &ex));
    check(lean_expr_mk_var(1, &e2, &ex));
    check(lean_expr_mk_var(0, &e3, &ex));
    check(lean_expr_eq(e1, e3, &b, &ex) && b);
    check(lean_expr_eq(e1, e2, &b, &ex) && !b);
    check(lean_expr_get_var_idx(e1, &i, &ex) && i == 0);
    check(lean_expr_get_var_idx(e2, &i, &ex) && i == 1);
    check(lean_expr_get_kind(e1) == LEAN_EXPR_VAR);
    check(lean_expr_get_kind(e2) == LEAN_EXPR_VAR);
    lean_expr_del(e1);
    lean_expr_del(e2);
    lean_expr_del(e3);
}

void test_const() {
    lean_exception ex;
    lean_name n1, n2, n3, n4;
    lean_univ u1;
    lean_list_univ l1, l2, l3, l4;
    lean_expr e1, e2, e3;
    lean_bool b;
    char const * s;
    check(lean_name_mk_anonymous(&n1, &ex));
    check(lean_name_mk_str(n1, "id", &n2, &ex));
    check(lean_name_mk_str(n1, "func", &n3, &ex));
    check(lean_univ_mk_zero(&u1, &ex));
    check(lean_list_univ_mk_nil(&l1, &ex));
    check(lean_list_univ_mk_cons(u1, l1, &l2, &ex));
    check(lean_list_univ_mk_cons(u1, l2, &l3, &ex));
    check(lean_expr_mk_const(n2, l2, &e1, &ex));
    check(lean_expr_mk_const(n2, l3, &e2, &ex));
    check(lean_expr_mk_const(n3, l3, &e3, &ex));
    check(lean_expr_eq(e1, e1, &b, &ex) && b);
    check(lean_expr_eq(e1, e2, &b, &ex) && !b);
    check(lean_expr_get_const_name(e2, &n4, &ex));
    check(lean_name_eq(n2, n4));
    check(lean_expr_get_const_univs(e3, &l4, &ex));
    check(lean_list_univ_eq(l3, l4, &b, &ex) && b);
    check(lean_expr_get_kind(e1) == LEAN_EXPR_CONST);
    check(lean_expr_get_kind(e2) == LEAN_EXPR_CONST);
    check(lean_expr_get_kind(e3) == LEAN_EXPR_CONST);
    check(lean_expr_to_string(e3, &s, &ex));
    printf("expr: %s\n", s);
    lean_name_del(n1);
    lean_name_del(n2);
    lean_name_del(n3);
    lean_name_del(n4);
    lean_univ_del(u1);
    lean_list_univ_del(l1);
    lean_list_univ_del(l2);
    lean_list_univ_del(l3);
    lean_list_univ_del(l4);
    lean_expr_del(e1);
    lean_expr_del(e2);
    lean_expr_del(e3);
    lean_string_del(s);
}

int main() {
    test_var();
    test_const();
    return 0;
}
