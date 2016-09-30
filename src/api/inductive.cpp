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

lean_bool lean_inductive_decl_mk(lean_name n, lean_list_name ps, unsigned nparams, lean_expr t, lean_list_expr cs, lean_inductive_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(ps);
    check_nonnull(t);
    check_nonnull(cs);
    for (expr const & c : to_list_expr_ref(cs)) {
        if (!is_local(c))
            throw exception("invalid inductive type, constructor must be a local constant");
    }
    *r = of_inductive_decl(new inductive_decl(to_name_ref(n), to_list_name_ref(ps), nparams, to_expr_ref(t), to_list_expr_ref(cs)));
    LEAN_CATCH;
}

void lean_inductive_decl_del(lean_inductive_decl t) {
    delete to_inductive_decl(t);
}

lean_bool lean_get_recursor_name(lean_name n, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    *r = of_name(new name(get_elim_name(to_name_ref(n))));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_name(lean_inductive_decl t, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    *r = of_name(new name(to_inductive_decl_ref(t).m_name));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_type(lean_inductive_decl t, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    *r = of_expr(new expr(to_inductive_decl_ref(t).m_type));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_constructors(lean_inductive_decl t, lean_list_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    *r = of_list_expr(new list<expr>(to_inductive_decl_ref(t).m_intro_rules));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_univ_params(lean_inductive_decl d, lean_list_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = of_list_name(new list<name>(to_inductive_decl_ref(d).m_level_params));
    LEAN_CATCH;
}

lean_bool lean_inductive_decl_get_num_params(lean_inductive_decl d, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = to_inductive_decl_ref(d).m_num_params;
    LEAN_CATCH;
}

lean_bool lean_env_add_inductive(lean_env env, lean_inductive_decl d, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(d);
    bool is_trusted = true;
    *r = of_env(new environment(module::add_inductive(to_env_ref(env), to_inductive_decl_ref(d), is_trusted)));
    LEAN_CATCH;
}

lean_bool lean_env_is_inductive_type(lean_env env, lean_name n, lean_inductive_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    if (auto d = is_inductive_decl(to_env_ref(env), to_name_ref(n))) {
        *r = of_inductive_decl(new inductive_decl(*d));
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

lean_bool lean_env_get_inductive_type_has_dep_elim(lean_env env, lean_name n, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(n);
    *r = has_dep_elim(to_env_ref(env), to_name_ref(n));
    LEAN_CATCH;
}
