/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/expr_lt.h"
#include "api/univ.h"
#include "api/expr.h"
#include "api/string.h"
#include "api/exception.h"
namespace lean {
void to_buffer(unsigned sz, lean_expr const * ns, buffer<expr> & r) {
    check_nonnull(ns);
    for (unsigned i = 0; i < sz; i++) {
        check_nonnull(ns[i]);
        r.push_back(to_expr_ref(ns[i]));
    }
}
}

using namespace lean; // NOLINT

lean_bool lean_expr_mk_var(unsigned i, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_expr(new expr(mk_var(i)));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_sort(lean_univ u, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    *r = of_expr(new expr(mk_sort(to_level_ref(u))));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_const(lean_name n, lean_list_univ us, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(us);
    *r = of_expr(new expr(mk_constant(to_name_ref(n), to_list_level_ref(us))));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_app(lean_expr f, lean_expr a, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(f);
    check_nonnull(a);
    *r = of_expr(new expr(mk_app(to_expr_ref(f), to_expr_ref(a))));
    LEAN_CATCH;
}

static binder_info to_binder_info(lean_binder_kind k) {
    switch (k) {
    case LEAN_BINDER_DEFAULT:         return binder_info();
    case LEAN_BINDER_IMPLICIT:        return mk_implicit_binder_info();
    case LEAN_BINDER_STRICT_IMPLICIT: return mk_strict_implicit_binder_info();
    case LEAN_BINDER_INST_IMPLICIT:   return mk_inst_implicit_binder_info();
    case LEAN_BINDER_HIDDEN:          return mk_contextual_info(false);
    }
    lean_unreachable();
}

static lean_binder_kind of_binder_info(binder_info k) {
    if (k.is_implicit())
        return LEAN_BINDER_IMPLICIT;
    else if (k.is_inst_implicit())
        return LEAN_BINDER_INST_IMPLICIT;
    else if (k.is_strict_implicit())
        return LEAN_BINDER_STRICT_IMPLICIT;
    else if (!k.is_contextual())
        return LEAN_BINDER_HIDDEN;
    else
        return LEAN_BINDER_DEFAULT;
}

lean_bool lean_expr_mk_lambda(lean_name n, lean_expr t, lean_expr b, lean_binder_kind k, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(t);
    check_nonnull(b);
    *r = of_expr(new expr(mk_lambda(to_name_ref(n), to_expr_ref(t), to_expr_ref(b), to_binder_info(k))));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_pi(lean_name n, lean_expr t, lean_expr b, lean_binder_kind k, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(t);
    check_nonnull(b);
    *r = of_expr(new expr(mk_pi(to_name_ref(n), to_expr_ref(t), to_expr_ref(b), to_binder_info(k))));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_macro(lean_macro_def m, lean_list_expr args, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(m);
    check_nonnull(args);
    buffer<expr> _args;
    to_buffer(to_list_expr_ref(args), _args);
    *r = of_expr(new expr(mk_macro(to_macro_definition_ref(m), _args.size(), _args.data())));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_local(lean_name n, lean_expr t, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(t);
    *r = of_expr(new expr(mk_local(to_name_ref(n), to_expr_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_local_ext(lean_name n, lean_name pp_n, lean_expr t, lean_binder_kind k, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(pp_n);
    check_nonnull(t);
    *r = of_expr(new expr(mk_local(to_name_ref(n), to_name_ref(pp_n), to_expr_ref(t), to_binder_info(k))));
    LEAN_CATCH;
}

lean_bool lean_expr_mk_metavar(lean_name n, lean_expr t, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    check_nonnull(t);
    *r = of_expr(new expr(mk_metavar(to_name_ref(n), to_expr_ref(t))));
    LEAN_CATCH;
}

lean_bool lean_expr_to_string(lean_expr e, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e);
    std::ostringstream out;
    out << to_expr_ref(e);
    *r = mk_string(out.str());
    LEAN_CATCH;
}

void lean_expr_del(lean_expr e) {
    delete to_expr(e);
}

void lean_macro_def_del(lean_macro_def m) {
    delete to_macro_definition(m);
}

lean_bool lean_macro_def_eq(lean_macro_def m1, lean_macro_def m2, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(m1);
    check_nonnull(m2);
    *r = to_macro_definition_ref(m1) == to_macro_definition_ref(m2);
    LEAN_CATCH;
}

lean_bool lean_macro_def_to_string(lean_macro_def m, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(m);
    std::ostringstream out;
    to_macro_definition_ref(m).display(out);
    *r = mk_string(out.str());
    LEAN_CATCH;
}

lean_expr_kind lean_expr_get_kind(lean_expr e) {
    if (!e)
        return LEAN_EXPR_VAR;
    switch (to_expr_ref(e).kind()) {
    case expr_kind::Var:       return LEAN_EXPR_VAR;
    case expr_kind::Sort:      return LEAN_EXPR_SORT;
    case expr_kind::Constant:  return LEAN_EXPR_CONST;
    case expr_kind::Meta:      return LEAN_EXPR_META;
    case expr_kind::Local:     return LEAN_EXPR_LOCAL;
    case expr_kind::App:       return LEAN_EXPR_APP;
    case expr_kind::Lambda:    return LEAN_EXPR_LAMBDA;
    case expr_kind::Pi:        return LEAN_EXPR_PI;
    case expr_kind::Macro:     return LEAN_EXPR_MACRO;
    }
    lean_unreachable();
}

lean_bool lean_expr_eq(lean_expr e1, lean_expr e2, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e1);
    check_nonnull(e2);
    *r = to_expr_ref(e1) == to_expr_ref(e2);
    LEAN_CATCH;
}

lean_bool lean_expr_lt(lean_expr e1, lean_expr e2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e1);
    check_nonnull(e2);
    *b = is_lt(to_expr_ref(e1), to_expr_ref(e2), false);
    LEAN_CATCH;
}

lean_bool lean_expr_quick_lt(lean_expr e1, lean_expr e2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(e1);
    check_nonnull(e2);
    *b = is_lt(to_expr_ref(e1), to_expr_ref(e2), true);
    LEAN_CATCH;
}

static void check_expr_kind(lean_expr e, lean_expr_kind k, char const * msg) {
    check_nonnull(e);
    if (lean_expr_get_kind(e) != k)
        throw exception(msg);
}

lean_bool lean_expr_get_var_idx(lean_expr e, unsigned * i, lean_exception * ex) {
    LEAN_TRY;
    check_expr_kind(e, LEAN_EXPR_VAR, "invalid argument, variable expected");
    *i = var_idx(to_expr_ref(e));
    LEAN_CATCH;
}

lean_bool lean_expr_get_sort_univ(lean_expr e, lean_univ * u, lean_exception * ex) {
    LEAN_TRY;
    check_expr_kind(e, LEAN_EXPR_SORT, "invalid argument, sort expected");
    *u = of_level(new level(sort_level(to_expr_ref(e))));
    LEAN_CATCH;
}

static void check_constant(lean_expr e) {
    check_expr_kind(e, LEAN_EXPR_CONST, "invalid argument, constant expected");
}

lean_bool lean_expr_get_const_name(lean_expr e, lean_name * n, lean_exception * ex) {
    LEAN_TRY;
    check_constant(e);
    *n = of_name(new name(const_name(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_const_univs(lean_expr e, lean_list_univ * us, lean_exception * ex) {
    LEAN_TRY;
    check_constant(e);
    *us = of_list_level(new list<level>(const_levels(to_expr_ref(e))));
    LEAN_CATCH;
}

static void check_app(lean_expr e) {
    check_expr_kind(e, LEAN_EXPR_APP, "invalid argument, function application expected");
}

lean_bool lean_expr_get_app_fun(lean_expr e, lean_expr * f, lean_exception * ex) {
    LEAN_TRY;
    check_app(e);
    *f = of_expr(new expr(app_fn(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_app_arg(lean_expr e, lean_expr * a, lean_exception * ex) {
    LEAN_TRY;
    check_app(e);
    *a = of_expr(new expr(app_arg(to_expr_ref(e))));
    LEAN_CATCH;
}

static void check_mlocal(lean_expr e) {
    check_nonnull(e);
    if (lean_expr_get_kind(e) != LEAN_EXPR_LOCAL && lean_expr_get_kind(e) != LEAN_EXPR_META)
        throw exception("invalid argument, local constant or meta-variable expected");
}

static void check_local(lean_expr e) {
    check_expr_kind(e, LEAN_EXPR_LOCAL, "invalid argument, local constant expected");
}

lean_bool lean_expr_get_mlocal_name(lean_expr e, lean_name * n, lean_exception * ex) {
    LEAN_TRY;
    check_mlocal(e);
    *n = of_name(new name(mlocal_name(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_mlocal_type(lean_expr e, lean_expr * t, lean_exception * ex) {
    LEAN_TRY;
    check_mlocal(e);
    *t = of_expr(new expr(mlocal_type(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_local_pp_name(lean_expr e, lean_name * n, lean_exception * ex) {
    LEAN_TRY;
    check_local(e);
    *n = of_name(new name(local_pp_name(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_local_binder_kind(lean_expr e, lean_binder_kind * k, lean_exception * ex) {
    LEAN_TRY;
    check_local(e);
    *k = of_binder_info(local_info(to_expr_ref(e)));
    LEAN_CATCH;
}

static void check_binding(lean_expr e) {
    check_nonnull(e);
    if (lean_expr_get_kind(e) != LEAN_EXPR_PI && lean_expr_get_kind(e) != LEAN_EXPR_LAMBDA)
        throw exception("invalid argument, lambda or Pi expression expected");
}

lean_bool lean_expr_get_binding_name(lean_expr e, lean_name * n, lean_exception * ex) {
    LEAN_TRY;
    check_binding(e);
    *n = of_name(new name(binding_name(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_binding_domain(lean_expr e, lean_expr * d, lean_exception * ex) {
    LEAN_TRY;
    check_binding(e);
    *d = of_expr(new expr(binding_domain(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_binding_body(lean_expr e, lean_expr * b, lean_exception * ex) {
    LEAN_TRY;
    check_binding(e);
    *b = of_expr(new expr(binding_body(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_binding_binder_kind(lean_expr e, lean_binder_kind * k, lean_exception * ex) {
    LEAN_TRY;
    check_binding(e);
    *k = of_binder_info(binding_info(to_expr_ref(e)));
    LEAN_CATCH;
}

static void check_macro(lean_expr e) {
    check_expr_kind(e, LEAN_EXPR_MACRO, "invalid argument, macro application expected");
}

lean_bool lean_expr_get_macro_def(lean_expr e, lean_macro_def * d, lean_exception * ex) {
    LEAN_TRY;
    check_macro(e);
    *d = of_macro_definition(new macro_definition(macro_def(to_expr_ref(e))));
    LEAN_CATCH;
}

lean_bool lean_expr_get_macro_args(lean_expr e, lean_list_expr * as, lean_exception * ex) {
    LEAN_TRY;
    check_macro(e);
    buffer<expr> args;
    args.append(macro_num_args(to_expr_ref(e)), macro_args(to_expr_ref(e)));
    *as = of_list_expr(new list<expr>(to_list(args)));
    LEAN_CATCH;
}

lean_bool lean_list_expr_mk_nil(lean_list_expr * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_list_expr(new list<expr>());
    LEAN_CATCH;
}

lean_bool lean_list_expr_mk_cons(lean_expr h, lean_list_expr t, lean_list_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(h);
    check_nonnull(t);
    *r = of_list_expr(new list<expr>(to_expr_ref(h), to_list_expr_ref(t)));
    LEAN_CATCH;
}

void lean_list_expr_del(lean_list_expr l) {
    delete to_list_expr(l);
}

lean_bool lean_list_expr_is_cons(lean_list_expr l) {
    return l && !is_nil(to_list_expr_ref(l));
}

lean_bool lean_list_expr_eq(lean_list_expr l1, lean_list_expr l2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l1);
    check_nonnull(l2);
    *b = to_list_expr_ref(l1) == to_list_expr_ref(l2);
    LEAN_CATCH;
}

lean_bool lean_list_expr_head(lean_list_expr l, lean_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l);
    if (!lean_list_expr_is_cons(l))
        throw lean::exception("invalid argument, non-nil list expected");
    *r = of_expr(new expr(head(to_list_expr_ref(l))));
    LEAN_CATCH;
}

lean_bool lean_list_expr_tail(lean_list_expr l, lean_list_expr * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l);
    if (!lean_list_expr_is_cons(l))
        throw lean::exception("invalid argument, non-nil list expected");
    *r = of_list_expr(new list<expr>(tail(to_list_expr_ref(l))));
    LEAN_CATCH;
}
