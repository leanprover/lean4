/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "api/string.h"
#include "api/exception.h"
#include "api/type_checker.h"
using namespace lean; // NOLINT

lean_bool lean_type_checker_mk(lean_env e, lean_type_checker * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    *r = of_type_checker(new type_checker(to_env_ref(e), name_generator()));
    LEAN_CATCH;
}

void lean_type_checker_del(lean_type_checker t) {
    delete to_type_checker(t);
}

void lean_cnstr_seq_del(lean_cnstr_seq s) {
    delete to_cnstr_seq(s);
}

lean_bool lean_type_checker_infer(lean_type_checker t, lean_expr e, lean_expr * r, lean_cnstr_seq * s, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    check_nonnull(e);
    auto ecs = to_type_checker_ref(t).infer(to_expr_ref(e));
    *r = of_expr(new expr(ecs.first));
    *s = of_cnstr_seq(new constraint_seq(ecs.second));
    LEAN_CATCH;
}

lean_bool lean_type_checker_check(lean_type_checker t, lean_expr e, lean_expr * r, lean_cnstr_seq * s, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    check_nonnull(e);
    auto ecs = to_type_checker_ref(t).check(to_expr_ref(e));
    *r = of_expr(new expr(ecs.first));
    *s = of_cnstr_seq(new constraint_seq(ecs.second));
    LEAN_CATCH;
}

lean_bool lean_type_checker_whnf(lean_type_checker t, lean_expr e, lean_expr * r, lean_cnstr_seq * s, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    check_nonnull(e);
    auto ecs = to_type_checker_ref(t).whnf(to_expr_ref(e));
    *r = of_expr(new expr(ecs.first));
    *s = of_cnstr_seq(new constraint_seq(ecs.second));
    LEAN_CATCH;
}

lean_bool lean_type_checker_is_def_eq(lean_type_checker t, lean_expr e1, lean_expr e2, lean_bool * r, lean_cnstr_seq * s, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(t);
    check_nonnull(e1);
    check_nonnull(e2);
    auto bcs = to_type_checker_ref(t).is_def_eq(to_expr_ref(e1), to_expr_ref(e2));
    *r = bcs.first;
    *s = of_cnstr_seq(new constraint_seq(bcs.second));
    LEAN_CATCH;
}
