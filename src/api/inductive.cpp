/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/module.h"
#include "api/decl.h"
#include "api/inductive.h"
#include "api/string.h"
#include "api/exception.h"
using namespace lean; // NOLINT
using namespace lean::inductive; // NOLINT

lean_bool lean_inductive_type_mk(lean_name n, lean_expr t, lean_list_expr cs, lean_inductive_type * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(t);
    check_nonnull(cs);
    for (expr const & c : to_list_expr_ref(cs)) {
        if (!is_local(c))
            throw exception("invalid inductive type, constructor must be a local constant");
    }
    *r = of_inductive_type(new inductive_decl(to_name_ref(n), to_expr_ref(t), to_list_expr_ref(cs)));
    LEAN_CATCH;
}

void lean_inductive_type_del(lean_inductive_type t) {
    delete to_inductive_type(t);
}

lean_bool lean_get_recursor_name(lean_name n, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    *r = of_name(new name(get_elim_name(to_name_ref(n))));
    LEAN_CATCH;
}

lean_bool lean_inductive_type_get_name(lean_inductive_type t, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    *r = of_name(new name(inductive_decl_name(to_inductive_type_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_inductive_type_get_type(lean_inductive_type t, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    *r = of_expr(new expr(inductive_decl_type(to_inductive_type_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_inductive_type_get_constructors(lean_inductive_type t, lean_list_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    *r = of_list_expr(new list<expr>(inductive_decl_intros(to_inductive_type_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_list_inductive_type_mk_nil(lean_list_inductive_type * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_list_inductive_type(new list<inductive_decl>());
    LEAN_CATCH;
}

lean_bool lean_list_inductive_type_mk_cons(lean_inductive_type h, lean_list_inductive_type t, lean_list_inductive_type * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(h);
    check_nonnull(t);
    *r = of_list_inductive_type(new list<inductive_decl>(to_inductive_type_ref(h), to_list_inductive_type_ref(t)));
    LEAN_CATCH;
}

void lean_list_inductive_type_del(lean_list_inductive_type l) {
    delete to_list_inductive_type(l);
}

lean_bool lean_list_inductive_type_is_cons(lean_list_inductive_type l) {
    return l && !is_nil(to_list_inductive_type_ref(l));
}

lean_bool lean_list_inductive_type_eq(lean_list_inductive_type l1, lean_list_inductive_type l2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l1);
    check_nonnull(l2);
    *b = to_list_inductive_type_ref(l1) == to_list_inductive_type_ref(l2);
    LEAN_CATCH;
}

lean_bool lean_list_inductive_type_head(lean_list_inductive_type l, lean_inductive_type * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l);
    if (!lean_list_inductive_type_is_cons(l))
        throw lean::exception("invalid argument, non-nil list expected");
    *r = of_inductive_type(new inductive_decl(head(to_list_inductive_type_ref(l))));
    LEAN_CATCH;
}

lean_bool lean_list_inductive_type_tail(lean_list_inductive_type l, lean_list_inductive_type * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l);
    if (!lean_list_inductive_type_is_cons(l))
        throw lean::exception("invalid argument, non-nil list expected");
    *r = of_list_inductive_type(new list<inductive_decl>(tail(to_list_inductive_type_ref(l))));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_mk(lean_list_name ps, unsigned n, lean_list_inductive_type ts, lean_inductive_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(ps);
    check_nonnull(ts);
    if (!lean_list_inductive_type_is_cons(ts))
        throw exception("invalid argument, non-nil list expected");
    *r = of_inductive_decl(new inductive_decls(to_list_name_ref(ps), n, to_list_inductive_type_ref(ts)));
    LEAN_CATCH;
}

void lean_inductive_decl_del(lean_inductive_decl d) {
    delete to_inductive_decl(d);
}

lean_bool lean_inductive_decl_get_univ_params(lean_inductive_decl d, lean_list_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = of_list_name(new list<name>(std::get<0>(to_inductive_decl_ref(d))));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_num_params(lean_inductive_decl d, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = std::get<1>(to_inductive_decl_ref(d));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_types(lean_inductive_decl d, lean_list_inductive_type * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = of_list_inductive_type(new list<inductive_decl>(std::get<2>(to_inductive_decl_ref(d))));
    LEAN_CATCH;
}

lean_bool lean_env_add_inductive(lean_env env, lean_inductive_decl d, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(d);
    level_param_names    ps = std::get<0>(to_inductive_decl_ref(d));
    unsigned             n  = std::get<1>(to_inductive_decl_ref(d));
    list<inductive_decl> ds = std::get<2>(to_inductive_decl_ref(d));
    *r = of_env(new environment(module::add_inductive(to_env_ref(env), ps, n, ds)));
    LEAN_CATCH;
}

lean_bool lean_env_is_inductive_type(lean_env env, lean_name n, lean_inductive_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = is_inductive_decl(to_env_ref(env), to_name_ref(n))) {
        *r = of_inductive_decl(new inductive_decls(*d));
        return lean_true;
    } else {
        return lean_false;
    }
    LEAN_CATCH;
}

lean_bool lean_env_is_constructor(lean_env env, lean_name n, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = is_intro_rule(to_env_ref(env), to_name_ref(n))) {
        *r = of_name(new name(*d));
        return lean_true;
    } else {
        return lean_false;
    }
    LEAN_CATCH;
}

lean_bool lean_env_is_recursor(lean_env env, lean_name n, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = is_elim_rule(to_env_ref(env), to_name_ref(n))) {
        *r = of_name(new name(*d));
        return lean_true;
    } else {
        return lean_false;
    }
    LEAN_CATCH;
}

lean_bool lean_env_get_inductive_type_num_indices(lean_env env, lean_name n, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = get_num_indices(to_env_ref(env), to_name_ref(n))) {
        *r = *d;
        return lean_true;
    } else {
        return lean_false;
    }
    LEAN_CATCH;
}

lean_bool lean_env_get_inductive_type_num_minor_premises(lean_env env, lean_name n, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = get_num_minor_premises(to_env_ref(env), to_name_ref(n))) {
        *r = *d;
        return lean_true;
    } else {
        return lean_false;
    }
    LEAN_CATCH;
}

lean_bool lean_env_get_inductive_type_num_type_formers(lean_env env, lean_name n, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = get_num_type_formers(to_env_ref(env), to_name_ref(n))) {
        *r = *d;
        return lean_true;
    } else {
        return lean_false;
    }
    LEAN_CATCH;
}

lean_bool lean_env_get_inductive_type_has_dep_elim(lean_env env, lean_name n, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    *r = has_dep_elim(to_env_ref(env), to_name_ref(n));
    LEAN_CATCH;
}
