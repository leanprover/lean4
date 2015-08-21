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

int main() {
    lean_exception ex;
    lean_name a, l, U, pp, pp_unicode, rn;
    lean_options o1, o2;
    lean_univ zero, one, p1, g1, m1, u, n, i, ru;
    lean_list_name ln1, ln2;
    lean_list_univ lu1, lu2;
    char const * s1;
    lean_bool r;

    check(lean_name_mk_anonymous(&a, &ex));
    check(lean_name_mk_str(a, "l_1", &l, &ex));
    check(lean_name_mk_str(a, "U", &U, &ex));
    check(lean_name_mk_str(a, "pp", &pp, &ex));
    check(lean_name_mk_str(pp, "unicode", &pp_unicode, &ex));

    check(lean_options_mk_empty(&o1, &ex));
    check(lean_options_set_bool(o1, pp_unicode, lean_false, &o2, &ex));

    check(lean_univ_mk_zero(&zero, &ex));
    check(lean_univ_mk_succ(zero, &one, &ex));
    check(lean_univ_mk_param(l, &p1, &ex));
    check(lean_univ_mk_global(U, &g1, &ex));
    check(lean_univ_mk_max(p1, one, &m1, &ex));
    check(lean_univ_mk_succ(m1, &u, &ex));

    check(lean_univ_normalize(u, &n, &ex));
    check(lean_univ_to_string(n, &s1, &ex));
    printf("universe: %s\n", s1);

    check(lean_univ_geq(one, zero, &r, &ex) && r);

    /* replace l_1 with one in u */
    check(lean_list_name_mk_nil(&ln1, &ex));
    check(lean_list_name_mk_cons(l, ln1, &ln2, &ex));
    check(lean_list_univ_mk_nil(&lu1, &ex));
    check(lean_list_univ_mk_cons(one, lu1, &lu2, &ex));
    check(lean_univ_instantiate(u, ln2, lu2, &i, &ex));
    lean_list_name_del(ln1);
    lean_list_name_del(ln2);
    lean_list_univ_del(lu1);
    lean_list_univ_del(lu2);
    lean_string_del(s1);
    check(lean_univ_to_string_using(i, o2, &s1, &ex));
    printf("universe: %s\n", s1);

    check(lean_univ_get_kind(zero) == LEAN_UNIV_ZERO);
    check(lean_univ_get_kind(one) == LEAN_UNIV_SUCC);
    check(lean_univ_get_kind(n) == LEAN_UNIV_MAX);

    check(lean_univ_get_name(g1, &rn, &ex) && lean_name_eq(rn, U));

    check(lean_univ_get_max_lhs(m1, &ru, &ex) && lean_univ_eq(ru, p1, &r, &ex) && r);
    lean_univ_del(ru);
    check(lean_univ_get_max_rhs(m1, &ru, &ex) && lean_univ_eq(ru, one, &r, &ex) && r);
    lean_univ_del(ru);
    check(lean_univ_get_pred(one, &ru, &ex) && lean_univ_eq(ru, zero, &r, &ex) && r);
    lean_univ_del(ru);

    lean_name_del(a);
    lean_name_del(l);
    lean_name_del(U);
    lean_name_del(pp);
    lean_name_del(pp_unicode);
    lean_name_del(rn);

    lean_options_del(o1);
    lean_options_del(o2);

    lean_univ_del(zero);
    lean_univ_del(one);
    lean_univ_del(p1);
    lean_univ_del(g1);
    lean_univ_del(m1);
    lean_univ_del(u);
    lean_univ_del(n);
    lean_univ_del(i);

    lean_string_del(s1);
    return 0;
}
