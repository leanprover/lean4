/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "api/string.h"
#include "api/exception.h"
#include "api/decl.h"
using namespace lean; // NOLINT

lean_bool lean_decl_mk_axiom(lean_name n, lean_list_name p, lean_expr t, lean_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(p);
    check_nonnull(t);
    *r = of_decl(new declaration(mk_axiom(to_name_ref(n), to_list_name_ref(p), to_expr_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_decl_mk_const(lean_name n, lean_list_name p, lean_expr t, lean_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(p);
    check_nonnull(t);
    *r = of_decl(new declaration(mk_constant_assumption(to_name_ref(n), to_list_name_ref(p), to_expr_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_decl_mk_def(lean_name n, lean_list_name p, lean_expr t, lean_expr v, unsigned h, lean_bool o, lean_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(p);
    check_nonnull(t);
    check_nonnull(v);
    *r = of_decl(new declaration(mk_definition(to_name_ref(n), to_list_name_ref(p), to_expr_ref(t), to_expr_ref(v), h, static_cast<bool>(o))));
    LEAN_CATCH;
}

lean_bool lean_decl_mk_def_with(lean_env e, lean_name n, lean_list_name p, lean_expr t, lean_expr v, lean_bool o, lean_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(n);
    check_nonnull(p);
    check_nonnull(t);
    check_nonnull(v);
    *r = of_decl(new declaration(mk_definition(to_env_ref(e), to_name_ref(n), to_list_name_ref(p), to_expr_ref(t), to_expr_ref(v), static_cast<bool>(o))));
    LEAN_CATCH;
}

lean_bool lean_decl_mk_thm(lean_name n, lean_list_name p, lean_expr t, lean_expr v, unsigned h, lean_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(p);
    check_nonnull(t);
    check_nonnull(v);
    *r = of_decl(new declaration(mk_theorem(to_name_ref(n), to_list_name_ref(p), to_expr_ref(t), to_expr_ref(v), h)));
    LEAN_CATCH;
}

lean_bool lean_decl_mk_thm_with(lean_env e, lean_name n, lean_list_name p, lean_expr t, lean_expr v, lean_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(n);
    check_nonnull(p);
    check_nonnull(t);
    check_nonnull(v);
    *r = of_decl(new declaration(mk_theorem(to_env_ref(e), to_name_ref(n), to_list_name_ref(p), to_expr_ref(t), to_expr_ref(v))));
    LEAN_CATCH;
}

void lean_decl_del(lean_decl d) {
    delete to_decl(d);
}

lean_decl_kind lean_decl_get_kind(lean_decl d) {
    if (!d)
        return LEAN_DECL_CONST;
    if (to_decl_ref(d).is_theorem())
        return LEAN_DECL_THM;
    else if (to_decl_ref(d).is_definition())
        return LEAN_DECL_DEF;
    else if (to_decl_ref(d).is_axiom())
        return LEAN_DECL_AXIOM;
    else if (to_decl_ref(d).is_constant_assumption())
        return LEAN_DECL_CONST;
    else
        return LEAN_DECL_CONST;
}

lean_bool lean_decl_get_name(lean_decl d, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = of_name(new name(to_decl_ref(d).get_name()));
    LEAN_CATCH;
}

lean_bool lean_decl_get_univ_params(lean_decl d, lean_list_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = of_list_name(new list<name>(to_decl_ref(d).get_univ_params()));
    LEAN_CATCH;
}

lean_bool lean_decl_get_type(lean_decl d, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(d);
    *r = of_expr(new expr(to_decl_ref(d).get_type()));
    LEAN_CATCH;
}

static void check_def_thm(lean_decl d) {
    check_nonnull(d);
    if (lean_decl_get_kind(d) != LEAN_DECL_DEF && lean_decl_get_kind(d) != LEAN_DECL_THM)
        throw exception("invalid argument, definition or theorem expected");
}

lean_bool lean_decl_get_value(lean_decl d, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_def_thm(d);
    *r = of_expr(new expr(to_decl_ref(d).get_value()));
    LEAN_CATCH;
}

lean_bool lean_decl_get_height(lean_decl d, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_def_thm(d);
    *r = to_decl_ref(d).get_height();
    LEAN_CATCH;
}

static void check_def(lean_decl d) {
    check_nonnull(d);
    if (lean_decl_get_kind(d) != LEAN_DECL_DEF)
        throw exception("invalid argument, definition expected");
}

lean_bool lean_decl_get_conv_opt(lean_decl d, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_def(d);
    *r = to_decl_ref(d).use_conv_opt();
    LEAN_CATCH;
}

lean_bool lean_decl_check(lean_env e, lean_decl d, lean_cert_decl * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    check_nonnull(d);
    *r = of_cert_decl(new certified_declaration(check(to_env_ref(e), to_decl_ref(d))));
    LEAN_CATCH;
}

void lean_cert_decl_del(lean_cert_decl d) {
    delete to_cert_decl(d);
}
