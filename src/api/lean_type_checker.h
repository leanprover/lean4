/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_TYPE_CHECKER_H
#define _LEAN_TYPE_CHECKER_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Type checker API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_type_checker);

/** \brief Create a type checker object for the given environment. */
lean_bool lean_type_checker_mk(lean_env e, lean_type_checker * r, lean_exception * ex);

/** \brief Dispose/delete the given type checker */
void lean_type_checker_del(lean_type_checker t);

/** \brief Infer the type of \c e using \c t. Store the result in \c r.
    \remark \c e must not contain any subterm v s.t. lean_expr_get_kind(v) == LEAN_EXPR_VAR
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_type_checker_infer(lean_type_checker t, lean_expr e, lean_expr * r, lean_exception * ex);

/** \brief Type check and infer the type of \c e using \c t. Store the result in \c r.
    \remark \c e must not contain any subterm v s.t. lean_expr_get_kind(v) == LEAN_EXPR_VAR
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_type_checker_check(lean_type_checker t, lean_expr e, lean_expr * r, lean_exception * ex);

/** \brief Compute the weak-head-normal-form of \c e using \c t. Store the result in \c r.
    \remark \c e must not contain any subterm v s.t. lean_expr_get_kind(v) == LEAN_EXPR_VAR
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_type_checker_whnf(lean_type_checker t, lean_expr e, lean_expr * r, lean_exception * ex);

/** \brief Store true in \c r iff \c e1 and \c e2 are definitionally equal.
    \remark \c e must not contain any subterm v s.t. lean_expr_get_kind(v) == LEAN_EXPR_VAR
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_type_checker_is_def_eq(lean_type_checker t, lean_expr e1, lean_expr e2, lean_bool * r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
