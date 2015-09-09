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

lean_expr mk_local(char const * n, lean_expr t) {
    lean_exception ex;
    lean_name _n = mk_name(n);
    lean_expr r;
    check(lean_expr_mk_local(_n, t, &r, &ex));
    lean_name_del(_n);
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
    lean_bool is_lt;

    check(lean_expr_lt(f, id_val, &is_lt, &ex) && is_lt);
    check(lean_expr_lt(id_val, f, &is_lt, &ex) && !is_lt);

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
    check(lean_univ_lt(zero, one, &is_lt, &ex) && is_lt);
    check(lean_univ_lt(one, zero, &is_lt, &ex) && !is_lt);
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

lean_univ mk_one() {
    lean_exception ex;
    lean_univ zero, one;
    check(lean_univ_mk_zero(&zero, &ex));
    check(lean_univ_mk_succ(zero, &one, &ex));
    lean_univ_del(zero);
    return one;
}

lean_univ mk_max(lean_univ u1, lean_univ u2) {
    lean_exception ex;
    lean_univ r;
    check(lean_univ_mk_max(u1, u2, &r, &ex));
    return r;
}

lean_expr mk_app(lean_expr f, lean_expr a) {
    lean_exception ex;
    lean_expr r;
    check(lean_expr_mk_app(f, a, &r, &ex));
    return r;
}

void test_inductive() {
    // declare list type
    lean_exception ex = 0;
    lean_env env         = mk_env();
    lean_name l_name     = mk_name("l");
    lean_univ l          = mk_uparam("l");
    lean_univ one        = mk_one();
    lean_univ m1l        = mk_max(one, l);
    lean_expr Typel      = mk_sort(l);
    lean_expr Typem1l    = mk_sort(m1l);
    lean_expr list_type  = mk_pi("A", Typel, Typem1l);
    lean_name list_name  = mk_name("list");
    lean_expr list       = mk_const("list", l);
    lean_expr v0         = mk_var(0);
    // nil : Pi (A : Type.{l}), list.{l} A
    lean_expr list_v0    = mk_app(list, v0);
    lean_expr nil_type   = mk_pi("A", Typel, list_v0);
    lean_expr nil        = mk_local("nil", nil_type);
    // cons : Pi (A : Type.{l}), A -> list.{l} A -> list.{l} A
    lean_expr v1         = mk_var(1);
    lean_expr v2         = mk_var(2);
    lean_expr list_v2    = mk_app(list, v2);
    lean_expr list_v1    = mk_app(list, v1);
    lean_expr cons_type1 = mk_pi("tail", list_v1, list_v2);
    lean_expr cons_type2 = mk_pi("head", v0, cons_type1);
    lean_expr cons_type  = mk_pi("A", Typel, cons_type2);
    lean_expr cons       = mk_local("cons", cons_type);
    //
    lean_list_expr cs1, cs2, list_cs;
    lean_inductive_type list_ind_type;
    lean_list_inductive_type li1, list_ind_types;
    lean_list_name ls1, ls;
    lean_inductive_decl list_decl;
    lean_env new_env;

    check(lean_list_name_mk_nil(&ls1, &ex));
    check(lean_list_name_mk_cons(l_name, ls1, &ls, &ex));

    check(lean_list_expr_mk_nil(&cs1, &ex));
    check(lean_list_expr_mk_cons(nil,  cs1, &cs2, &ex));
    check(lean_list_expr_mk_cons(cons, cs2, &list_cs, &ex));

    check(lean_inductive_type_mk(list_name, list_type, list_cs, &list_ind_type, &ex));

    check(lean_list_inductive_type_mk_nil(&li1, &ex));
    check(lean_list_inductive_type_mk_cons(list_ind_type, li1, &list_ind_types, &ex));

    check(lean_inductive_decl_mk(ls, 1, list_ind_types, &list_decl, &ex));

    check(lean_env_add_inductive(env, list_decl, &new_env, &ex));

    {
        unsigned n;
        lean_inductive_decl d;
        lean_name cons_name = mk_name("cons");
        lean_name r_name;
        lean_list_inductive_type types;
        check(lean_env_get_inductive_type_num_indices(new_env, list_name, &n, &ex) && n == 0);
        check(lean_env_get_inductive_type_num_minor_premises(new_env, list_name, &n, &ex) && n == 2);
        check(!lean_env_is_inductive_type(env, list_name, &d, &ex));
        check(lean_env_is_inductive_type(new_env, list_name, &d, &ex));
        check(lean_inductive_decl_get_num_params(d, &n, &ex) && n == 1);
        check(lean_inductive_decl_get_types(d, &types, &ex));
        check(lean_list_inductive_type_is_cons(types));
        check(lean_env_is_constructor(new_env, cons_name, &r_name, &ex) && lean_name_eq(list_name, r_name));
        lean_list_inductive_type_del(types);
        lean_inductive_decl_del(d);
        lean_name_del(cons_name);
        lean_name_del(r_name);
    }

    lean_env_del(env);
    lean_name_del(list_name);
    lean_name_del(l_name);
    lean_univ_del(l);
    lean_univ_del(one);
    lean_univ_del(m1l);
    lean_expr_del(Typel);
    lean_expr_del(Typem1l);
    lean_expr_del(list_type);
    lean_expr_del(list);
    lean_expr_del(v0);
    lean_expr_del(list_v0);
    lean_expr_del(nil_type);
    lean_expr_del(nil);
    lean_expr_del(v1);
    lean_expr_del(v2);
    lean_expr_del(list_v2);
    lean_expr_del(list_v1);
    lean_expr_del(cons_type1);
    lean_expr_del(cons_type2);
    lean_expr_del(cons_type);
    lean_expr_del(cons);
    lean_list_expr_del(cs1);
    lean_list_expr_del(cs2);
    lean_list_expr_del(list_cs);
    lean_inductive_type_del(list_ind_type);
    lean_list_inductive_type_del(li1);
    lean_list_inductive_type_del(list_ind_types);
    lean_list_name_del(ls1);
    lean_list_name_del(ls);
    lean_inductive_decl_del(list_decl);
    lean_env_del(new_env);
}

void test_parser() {
    lean_exception ex = 0;
    lean_env env      = mk_env();
    lean_ios ios;
    lean_env new_env;
    lean_ios new_ios;
    lean_options o;
    check(lean_options_mk_empty(&o, &ex));
    check(lean_ios_mk_std(o, &ios, &ex));
    check(lean_parse_commands(env, ios, "import standard open nat definition double (a : nat) := a + a check double 4 eval double 4",
                              &new_env, &new_ios, &ex));
    {
        lean_name double_name = mk_name("double");
        lean_decl double_decl;
        lean_expr double_decl_value;
        char const * s;
        check(lean_env_get_decl(new_env, double_name, &double_decl, &ex));
        check(lean_decl_get_value(double_decl, &double_decl_value, &ex));
        check(lean_expr_to_pp_string(new_env, new_ios, double_decl_value, &s, &ex));
        printf("definition of double\n%s\n", s);
        lean_name_del(double_name);
        lean_decl_del(double_decl);
        lean_expr_del(double_decl_value);
        lean_string_del(s);
    }

    {
        lean_expr e;
        lean_list_name ps;
        // remark: we can use notation from the namespace nat because we have executed 'open nat'
        // when we created new_env
        check(lean_parse_expr(new_env, new_ios, "double (2 + 3)", &e, &ps, &ex));
        char const * s;
        check(lean_expr_to_pp_string(new_env, new_ios, e, &s, &ex));
        printf("parsed expression: %s\n", s);
        lean_string_del(s);
        lean_expr_del(e);
        lean_list_name_del(ps);
    }

    lean_options_del(o);
    lean_env_del(env);
    lean_env_del(new_env);
    lean_ios_del(ios);
    lean_ios_del(new_ios);
}

void test_parser_error() {
    lean_exception ex = 0;
    lean_env env      = mk_env();
    lean_ios ios;
    lean_env new_env;
    lean_ios new_ios;
    lean_options o;
    check(lean_options_mk_empty(&o, &ex));
    check(lean_ios_mk_std(o, &ios, &ex));
    check(!lean_parse_commands(env, ios, "import data.nat open nat definition double (a : nat) := a + true",
                               &new_env, &new_ios, &ex));
    {
        lean_exception ex2 = 0;
        char const * s1 = lean_exception_get_message(ex);
        char const * s2 = lean_exception_get_detailed_message(ex);
        char const * s3;
        printf("\nexception kind: %d\n", lean_exception_get_kind(ex));
        printf("exception message: %s\n", s1);
        printf("exception detailed message: %s\n", s2);
        check(lean_exception_to_pp_string(env, ios, ex, &s3, &ex2));
        printf("exception: %s\n", s3);
        lean_string_del(s1);
        lean_string_del(s2);
        lean_string_del(s3);
    }
    lean_options_del(o);
    lean_exception_del(ex);
    lean_env_del(env);
    lean_ios_del(ios);
}


int main() {
    test_add_univ();
    test_id();
    test_path();
    test_import();
    test_inductive();
    test_parser();
    test_parser_error();
    return 0;
}
