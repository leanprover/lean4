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

lean_name mk_name(char const * n) {
    lean_exception ex;
    lean_name a, r;
    check(lean_name_mk_anonymous(&a, &ex));
    check(lean_name_mk_str(a, n, &r, &ex));
    lean_name_del(a);
    return r;
}

lean_univ mk_uparam(char const * n) {
    lean_exception ex;
    lean_univ r;
    lean_name _n = mk_name(n);
    check(lean_univ_mk_param(_n, &r, &ex));
    lean_name_del(_n);
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

lean_expr mk_constant(char const * n, lean_list_univ us) {
    lean_exception ex;
    lean_name _n = mk_name(n);
    lean_expr r;
    check(lean_expr_mk_const(_n, us, &r, &ex));
    lean_name_del(_n);
    return r;
}

lean_expr mk_var(unsigned i) {
   lean_exception ex;
   lean_expr r;
   check(lean_expr_mk_var(i, &r, &ex));
   return r;
}

lean_expr mk_sort(lean_univ u) {
   lean_exception ex;
   lean_expr r;
   check(lean_expr_mk_sort(u, &r, &ex));
   return r;
}

/** create a constant with a single universe parameter */
lean_expr mk_const(char const * n, lean_univ u) {
    lean_exception ex;
    lean_name _n = mk_name(n);
    lean_list_univ l1, l2;
    check(lean_list_univ_mk_nil(&l1, &ex));
    check(lean_list_univ_mk_cons(u, l1, &l2, &ex));
    lean_expr r;
    check(lean_expr_mk_const(_n, l2, &r, &ex));
    lean_name_del(_n);
    lean_list_univ_del(l1);
    lean_list_univ_del(l2);
    return r;
}


lean_expr mk_pi(char const * n, lean_expr d, lean_expr c) {
    lean_exception ex;
    lean_name name = mk_name(n);
    lean_expr r;
    check(lean_expr_mk_pi(name, d, c, LEAN_BINDER_DEFAULT, &r, &ex));
    lean_name_del(name);
    return r;
}

lean_expr mk_lambda(char const * n, lean_expr d, lean_expr c) {
    lean_exception ex;
    lean_name name = mk_name(n);
    lean_expr r;
    check(lean_expr_mk_lambda(name, d, c, LEAN_BINDER_DEFAULT, &r, &ex));
    lean_name_del(name);
    return r;
}

lean_decl mk_def(char const * n, lean_list_name p, lean_expr t, lean_expr v) {
    lean_exception ex;
    lean_name name = mk_name(n);
    lean_decl r;
    check(lean_decl_mk_def(name, p, t, v, 0, lean_true, &r, &ex));
    lean_name_del(name);
    return r;
}

void print_univ_and_del(lean_name n) {
    lean_exception ex;
    char const * s;
    check(lean_name_to_string(n, &s, &ex));
    printf("universe: %s\n", s);
    lean_string_del(s);
    lean_name_del(n);
}

void print_expr(lean_expr e) {
    lean_exception ex;
    char const * s;
    check(lean_expr_to_string(e, &s, &ex));
    printf("%s\n", s);
    lean_string_del(s);
}

void print_decl_and_del(lean_decl d) {
    lean_exception ex;
    lean_name n;
    lean_expr t;
    char const * s;
    check(lean_decl_get_name(d, &n, &ex));
    check(lean_name_to_string(n, &s, &ex));
    printf("declaration name: %s\n", s);
    check(lean_decl_get_type(d, &t, &ex));
    printf("  type: ");
    print_expr(t);
    if (lean_decl_get_kind(d) == LEAN_DECL_DEF || lean_decl_get_kind(d) == LEAN_DECL_THM) {
        lean_expr v;
        check(lean_decl_get_value(d, &v, &ex));
        printf("  value: ");
        print_expr(v);
        lean_expr_del(v);
    }
    lean_expr_del(t);
    lean_name_del(n);
    lean_string_del(s);
    lean_decl_del(d);
}

void test_add_univ() {
    lean_exception ex;
    lean_name u  = mk_name("u");
    lean_name v  = mk_name("v");
    lean_env env = mk_env();
    lean_env new_env;
    check(lean_env_add_univ(env, u, &new_env, &ex));
    check(lean_env_contains_univ(new_env, u));
    check(!lean_env_contains_univ(new_env, v));
    check(lean_env_for_each_univ(new_env, print_univ_and_del, &ex));
    lean_name_del(u);
    lean_name_del(v);
    lean_env_del(env);
    lean_env_del(new_env);
}

void test_id() {
    lean_exception ex;
    lean_univ l          = mk_uparam("l");
    lean_env env         = mk_env();
    lean_expr v0         = mk_var(0);
    lean_expr v1         = mk_var(1);
    lean_expr AA         = mk_pi("a", v0, v1);
    lean_expr Type       = mk_sort(l);
    lean_expr id_type    = mk_pi("A", Type, AA);
    lean_expr f          = mk_lambda("a", v0, v0);
    lean_expr id_val     = mk_lambda("A", Type, f);
    lean_name l_name     = mk_name("l");
    lean_list_name id_ps = mk_unary_name_list(l_name);
    lean_decl id_def     = mk_def("id", id_ps, id_type, id_val);
    lean_name id_name    = mk_name("id");
    lean_cert_decl id_cert_def;
    lean_env new_env;
    lean_univ zero, one;

    printf("id type:  ");
    print_expr(id_type);
    printf("id value: ");
    print_expr(id_val);
    printf("-------\n");

    /* type check definition */
    check(lean_decl_check(env, id_def, &id_cert_def, &ex));
    /* add certified definition to environment */
    check(lean_env_add(env, id_cert_def, &new_env, &ex));

    check(!lean_env_contains_decl(env, id_name));
    check(lean_env_contains_decl(new_env, id_name));
    check(lean_env_for_each_decl(new_env, print_decl_and_del, &ex));

    check(lean_univ_mk_zero(&zero, &ex));
    check(lean_univ_mk_succ(zero, &one, &ex));
    {
        lean_type_checker tc;
        lean_expr T0  = mk_sort(zero);
        lean_expr T1  = mk_sort(one);
        lean_expr id1 = mk_const("id", one);
        lean_expr id1T1, id1T1T0;
        lean_expr n1;
        lean_cnstr_seq s1;
        check(lean_expr_mk_app(id1, T1, &id1T1, &ex));
        check(lean_expr_mk_app(id1T1, T0, &id1T1T0, &ex));
        check(lean_type_checker_mk(new_env, &tc, &ex));
        printf("WHNF test\n");
        print_expr(id1T1T0);
        check(lean_type_checker_whnf(tc, id1T1T0, &n1, &s1, &ex));
        printf("=====>\n");
        print_expr(n1);
        lean_expr_del(n1);
        lean_cnstr_seq_del(s1);

        printf("Infer type test\n");
        print_expr(id1T1);
        check(lean_type_checker_infer(tc, id1T1, &n1, &s1, &ex));
        printf("=====>\n");
        print_expr(n1);
        lean_expr_del(n1);
        lean_cnstr_seq_del(s1);

        lean_type_checker_del(tc);
        lean_expr_del(T0);
        lean_expr_del(T1);
        lean_expr_del(id1);
        lean_expr_del(id1T1);
        lean_expr_del(id1T1T0);
    }

    lean_univ_del(l);
    lean_env_del(env);
    lean_expr_del(v0);
    lean_expr_del(v1);
    lean_expr_del(Type);
    lean_expr_del(AA);
    lean_expr_del(id_type);
    lean_expr_del(f);
    lean_expr_del(id_val);
    lean_decl_del(id_def);
    lean_list_name_del(id_ps);
    lean_name_del(l_name);
    lean_cert_decl_del(id_cert_def);
    lean_env_del(new_env);
    lean_name_del(id_name);
    lean_univ_del(zero);
    lean_univ_del(one);
}

void test_path() {
    lean_exception ex;
    char const * p;
    check(lean_get_std_path(&p, &ex));
    printf("LEAN_PATH: %s\n", p);
    lean_string_del(p);
    check(lean_get_hott_path(&p, &ex));
    printf("HLEAN_PATH: %s\n", p);
    lean_string_del(p);
}

void print_decl_name_and_del(lean_decl d) {
    lean_exception ex;
    lean_name n;
    char const * s;
    check(lean_decl_get_name(d, &n, &ex));
    check(lean_name_to_string(n, &s, &ex));
    printf("declaration name: %s\n", s);
    lean_name_del(n);
    lean_string_del(s);
    lean_decl_del(d);
}

void test_import() {
    lean_exception ex;
    lean_env  env = mk_env();
    lean_name std = mk_name("standard");
    lean_list_name ms = mk_unary_name_list(std);
    lean_options o;
    lean_ios ios;
    lean_env new_env;
    lean_decl nat_gcd_decl;
    lean_name nat = mk_name("nat");
    lean_name nat_gcd;
    lean_expr nat_gcd_val;
    char const * s;
    check(lean_options_mk_empty(&o, &ex));
    check(lean_ios_mk_std(o, &ios, &ex));
    check(lean_env_import(env, ios, ms, &new_env, &ex));
    check(lean_env_for_each_decl(new_env, print_decl_name_and_del, &ex));

    check(lean_name_mk_str(nat, "gcd", &nat_gcd, &ex));
    check(lean_env_get_decl(new_env, nat_gcd, &nat_gcd_decl, &ex));
    check(lean_decl_get_value(nat_gcd_decl, &nat_gcd_val, &ex));
    check(lean_expr_to_pp_string(new_env, ios, nat_gcd_val, &s, &ex));
    printf("nat.gcd\n%s\n", s);
    lean_env_del(env);
    lean_name_del(std);
    lean_list_name_del(ms);
    lean_options_del(o);
    lean_ios_del(ios);
    lean_env_del(new_env);
    lean_name_del(nat);
    lean_name_del(nat_gcd);
    lean_decl_del(nat_gcd_decl);
    lean_expr_del(nat_gcd_val);
    lean_string_del(s);
}

int main() {
    test_add_univ();
    test_id();
    test_path();
    test_import();
    return 0;
}
