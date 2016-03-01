/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_EXPR_H
#define _LEAN_EXPR_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Expression API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_macro_def);
LEAN_DEFINE_TYPE(lean_expr);
LEAN_DEFINE_TYPE(lean_list_expr);

typedef enum {
    LEAN_EXPR_VAR,
    LEAN_EXPR_SORT,
    LEAN_EXPR_CONST,
    LEAN_EXPR_LOCAL,
    LEAN_EXPR_META,
    LEAN_EXPR_APP,
    LEAN_EXPR_LAMBDA,
    LEAN_EXPR_PI,
    LEAN_EXPR_LET,
    LEAN_EXPR_MACRO,
} lean_expr_kind;

typedef enum {
    LEAN_BINDER_DEFAULT,           // (x : A)
    LEAN_BINDER_IMPLICIT,          // {x : A}
    LEAN_BINDER_STRICT_IMPLICIT,   // {{x : A}}
    LEAN_BINDER_INST_IMPLICIT      // [x : A]
} lean_binder_kind;

/** \brief Create a variable with de-Bruijn index \c i.
    This is a bounded variable. */
lean_bool lean_expr_mk_var(unsigned i, lean_expr * r, lean_exception * ex);
/** \brief r := Type.{u} */
lean_bool lean_expr_mk_sort(lean_univ u, lean_expr * r, lean_exception * ex);
/** \brief Create a constant with name \c n and universe parameters <tt>us[0], ..., us[sz-1]</tt>,
    and store the result in \c r. */
lean_bool lean_expr_mk_const(lean_name n, lean_list_univ us, lean_expr * r, lean_exception * ex);
/** \brief Create a function application, r := f a */
lean_bool lean_expr_mk_app(lean_expr f, lean_expr a, lean_expr * r, lean_exception * ex);
/** \brief Create a lambda abstraction, r := (fun n : t, b)
    \remark The parameter \c k specifies the kind of binder annotation (i.e., it corresponds to (), {}, {{}}, [] decorations in the lean front-end) */
lean_bool lean_expr_mk_lambda(lean_name n, lean_expr t, lean_expr b, lean_binder_kind k, lean_expr * r, lean_exception * ex);
/** \brief Create a Pi abstraction, r := (Pi n : t, b)
    \remark The parameter \c k specifies the kind of binder annotation (i.e., it corresponds to (), {}, {{}}, [] decorations in the lean front-end) */
lean_bool lean_expr_mk_pi(lean_name n, lean_expr t, lean_expr b, lean_binder_kind k, lean_expr * r, lean_exception * ex);
/** \brief Create a macro application */
lean_bool lean_expr_mk_macro(lean_macro_def m, lean_list_expr args, lean_expr * r, lean_exception * ex);
/** \brief Create a local constant with name \c n and type \c t, and store the result in \c r.
    \remark We use local constants to represent free variables. */
lean_bool lean_expr_mk_local(lean_name n, lean_expr t, lean_expr * r, lean_exception * ex);
/** \brief Create a local constant with internal name \c n and pretty print name \c pp_n, and type \c t, and store the result in \c r.
    \remark We use local constants to represent free variables.
    \remark The parameter \c k specifies the kind of binder annotation (i.e., it corresponds to (), {}, {{}}, [] decorations in the lean front-end). */
lean_bool lean_expr_mk_local_ext(lean_name n, lean_name pp_n, lean_expr t, lean_binder_kind k, lean_expr * r, lean_exception * ex);
/** \brief Create a meta-variable (aka unification variable) with name \c n and type \c t, and store the result in \c r. */
lean_bool lean_expr_mk_metavar(lean_name n, lean_expr t, lean_expr * r, lean_exception * ex);

/** \brief Delete/dispose the given macro definition. */
void lean_macro_def_del(lean_macro_def m);
/** \brief Store \c lean_true in \c r iff the two given macro definitions are equal. */
lean_bool lean_macro_def_eq(lean_macro_def m1, lean_macro_def m2, lean_bool * r, lean_exception * ex);
/** \brief Store in \c r a (crude) string representation of the given macro definition.
    \remark \c r must be deleted using #lean_string_del. */
lean_bool lean_macro_def_to_string(lean_macro_def m, char const ** r, lean_exception * ex);

/** \brief Store in \c r a (crude) string representation of the given expression.
    \remark \c r must be deleted using #lean_string_del.
    \remark To use the nicer pretty printer, we have an API that also takes a lean_environment object as argument. */
lean_bool lean_expr_to_string(lean_expr e, char const ** r, lean_exception * ex);
/** \brief Delete/dispose the given expression. */
void lean_expr_del(lean_expr e);
/** \brief Return the kind of the given expression.
    \remark Return LEAN_EXPR_VAR if e is null. */
lean_expr_kind lean_expr_get_kind(lean_expr e);
/** \brief Store \c lean_true in \c r iff the two given expressions are equal. */
lean_bool lean_expr_eq(lean_expr e1, lean_expr e2, lean_bool * r, lean_exception * ex);
/** \brief Store true in \c b if \c e1 is smaller than \c e2 in the internal total order. */
lean_bool lean_expr_lt(lean_expr e1, lean_expr e2, lean_bool * b, lean_exception * ex);
/** \brief Store true in \c b if \c e1 is smaller than \c e2 in the internal total order.
    Similar to #lean_expr_lt, but it is more efficient because it first compares
    the hashcodes associated with \c e1 and \c e2. */
lean_bool lean_expr_quick_lt(lean_expr e1, lean_expr e2, lean_bool * b, lean_exception * ex);

/** \brief Store in \c i the de-Brujin index of the given variable.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_VAR
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_var_idx(lean_expr e, unsigned * i, lean_exception * ex);
/** \brief Stgore in \c u the universe of the given sort.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_SORT
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_sort_univ(lean_expr e, lean_univ * u, lean_exception * ex);
/** \brief Store in \c n the name of the given constant.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_CONST
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_const_name(lean_expr e, lean_name * n, lean_exception * ex);
/** \brief Store in \c us the universes parameters of the given constant.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_CONST
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_const_univs(lean_expr e, lean_list_univ * us, lean_exception * ex);
/** \brief Store in \c f the function of the given function application.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_APP
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_app_fun(lean_expr e, lean_expr * f, lean_exception * ex);
/** \brief Store in \c a the argument of the given function application.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_APP
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_app_arg(lean_expr e, lean_expr * a, lean_exception * ex);
/** \brief Store in \c n the name the given local constant or meta-variable.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LOCAL || lean_expr_get_kind(e) == LEAN_EXPR_META
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_mlocal_name(lean_expr e, lean_name * n, lean_exception * ex);
/** \brief Store in \c t the type the given local constant or meta-variable.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LOCAL || lean_expr_get_kind(e) == LEAN_EXPR_META
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_mlocal_type(lean_expr e, lean_expr * t, lean_exception * ex);
/** \brief Store in \c n the pretty printing name the given local constant.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LOCAL
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_local_pp_name(lean_expr e, lean_name * n, lean_exception * ex);
/** \brief Store in \c k the binder_kind associated with the given local constant.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LOCAL
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_local_binder_kind(lean_expr e, lean_binder_kind * k, lean_exception * ex);
/** \brief Store in \c n the name associated with the given binding expression (i.e., lambda or Pi).
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LAMBDA || lean_expr_get_kind(e) == LEAN_EXPR_PI
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_binding_name(lean_expr e, lean_name * n, lean_exception * ex);
/** \brief Store in \c d the domain of the given binding (i.e., lambda or Pi).
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LAMBDA || lean_expr_get_kind(e) == LEAN_EXPR_PI
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_binding_domain(lean_expr e, lean_expr * d, lean_exception * ex);
/** \brief Store in \c b the body of the given binding (i.e., lambda or Pi).
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LAMBDA || lean_expr_get_kind(e) == LEAN_EXPR_PI
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_binding_body(lean_expr e, lean_expr * b, lean_exception * ex);
/** \brief Store in \c k the binder_kind of the given binding (i.e., lambda or Pi).
    \pre lean_expr_get_kind(e) == LEAN_EXPR_LAMBDA || lean_expr_get_kind(e) == LEAN_EXPR_PI
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_binding_binder_kind(lean_expr e, lean_binder_kind * k, lean_exception * ex);
/** \brief Store in \c d the macro definition of the given macro application.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_MACRO
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_macro_def(lean_expr e, lean_macro_def * d, lean_exception * ex);
/** \brief Store in \c as the arguments of the given macro application.
    \pre lean_expr_get_kind(e) == LEAN_EXPR_MACRO
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_expr_get_macro_args(lean_expr e, lean_list_expr * as, lean_exception * ex);

/** \brief Create the empty list of exprs */
lean_bool lean_list_expr_mk_nil(lean_list_expr * r, lean_exception * ex);
/** \brief Create the list <tt>h :: t</tt> */
lean_bool lean_list_expr_mk_cons(lean_expr h, lean_list_expr t, lean_list_expr * r, lean_exception * ex);
/** \brief Delete/dispose the given list of exprs */
void lean_list_expr_del(lean_list_expr l);
/** \brief Return true iff the list is a "cons" (i.e., it is not the nil list) */
lean_bool lean_list_expr_is_cons(lean_list_expr l);
/** \brief Return true in \c b iff the two given lists are equal */
lean_bool lean_list_expr_eq(lean_list_expr n1, lean_list_expr n2, lean_bool * b, lean_exception * ex);
/** \brief Store in \c r the head of the given list
    \pre lean_list_expr_is_cons(l)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_list_expr_head(lean_list_expr l, lean_expr * r, lean_exception * ex);
/** \brief Store in \c r the tail of the given list
    \pre lean_list_expr_is_cons(l)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_list_expr_tail(lean_list_expr l, lean_list_expr * r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
