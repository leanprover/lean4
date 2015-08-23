/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "library/standard_kernel.h"
#include "library/hott_kernel.h"
#include "library/module.h"
#include "api/decl.h"
#include "api/string.h"
#include "api/exception.h"
#include "api/lean_env.h"
using namespace lean; // NOLINT

lean_bool lean_env_mk_std(unsigned t, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_env(new environment(mk_environment(t)));
    LEAN_CATCH;
}

lean_bool lean_env_mk_hott(unsigned t, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_env(new environment(mk_hott_environment(t)));
    LEAN_CATCH;
}

lean_bool lean_env_add_univ(lean_env e, lean_name u, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(u);
    *r = of_env(new environment(module::add_universe(to_env_ref(e), to_name_ref(u))));
    LEAN_CATCH;
}

lean_bool lean_env_add(lean_env e, lean_cert_decl d, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(d);
    *r = of_env(new environment(module::add(to_env_ref(e), to_cert_decl_ref(d))));
    LEAN_CATCH;
}

lean_bool lean_env_replace(lean_env e, lean_cert_decl d, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(d);
    *r = of_env(new environment(to_env_ref(e).replace(to_cert_decl_ref(d))));
    LEAN_CATCH;
}

void lean_env_del(lean_env e) {
    delete to_env(e);
}

unsigned lean_env_trust_level(lean_env e) {
    return e ? to_env_ref(e).trust_lvl() : 0;
}

lean_bool lean_env_proof_irrel(lean_env e) {
    return e && to_env_ref(e).prop_proof_irrel();
}

lean_bool lean_env_impredicative(lean_env e) {
    return e && to_env_ref(e).impredicative();
}

lean_bool lean_env_contains_univ(lean_env e, lean_name n) {
    return e && n && to_env_ref(e).is_universe(to_name_ref(n));
}

lean_bool lean_env_contains_decl(lean_env e, lean_name n) {
    return e && n && to_env_ref(e).find(to_name_ref(n));
}

lean_bool lean_env_get_decl(lean_env e, lean_name n, lean_decl * d, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(n);
    *d = of_decl(new declaration(to_env_ref(e).get(to_name_ref(n))));
    LEAN_CATCH;
}

lean_bool lean_env_is_descendant(lean_env e1, lean_env e2) {
    return e1 && e2 && to_env_ref(e1).is_descendant(to_env_ref(e2));
}

lean_bool lean_env_forget(lean_env e, lean_env * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    *r = of_env(new environment(to_env_ref(e).forget()));
    LEAN_CATCH;
}

lean_bool lean_env_for_each_decl(lean_env e, void (*f)(lean_decl), lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    to_env_ref(e).for_each_declaration([&](declaration const & d) {
            f(of_decl(new declaration(d)));
        });
    return lean_true;
    LEAN_CATCH;
}

lean_bool lean_env_for_each_univ(lean_env e, void (*f)(lean_name), lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    to_env_ref(e).for_each_universe([&](name const & u) {
            f(of_name(new name(u)));
        });
    return lean_true;
    LEAN_CATCH;
}
