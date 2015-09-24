/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_DECL_H
#define _LEAN_DECL_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Declaration API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_env);
LEAN_DEFINE_TYPE(lean_decl);
LEAN_DEFINE_TYPE(lean_cert_decl);

typedef enum {
    LEAN_DECL_CONST,
    LEAN_DECL_AXIOM,
    LEAN_DECL_DEF,
    LEAN_DECL_THM
} lean_decl_kind;

/** \brief Create an axiom with name \c n, universe parameters names \c p, and type \c t
    \remark Recall that declarations are universe polymorphic in Lean. */
lean_bool lean_decl_mk_axiom(lean_name n, lean_list_name p, lean_expr t, lean_decl * r, lean_exception * ex);
/** \brief Create an constant with name \c n, universe parameters names \c p, and type \c t
    \remark Constants and axioms are essentially the same thing in Lean. */
lean_bool lean_decl_mk_const(lean_name n, lean_list_name p, lean_expr t, lean_decl * r, lean_exception * ex);
/** \brief Create a definition with name \c n, universe parameters names \c p, type \c t, value \c v,
    definitional height \c h and a flag \c o indicating whether normalization will lazily unfold it or not. */
lean_bool lean_decl_mk_def(lean_name n, lean_list_name p, lean_expr t, lean_expr v, unsigned h, lean_bool o, lean_decl * r, lean_exception * ex);
/** \brief Create a definition with name \c n, universe parameters names \c p, type \c t, value \c v,
    and a flag \c o indicating whether normalization will lazily unfold it or not.
    \remark The definitional height is computed using the information in the given environment. */
lean_bool lean_decl_mk_def_with(lean_env e, lean_name n, lean_list_name p, lean_expr t, lean_expr v, lean_bool o, lean_decl * r, lean_exception * ex);
/** \brief Create a theorem with name \c n, universe parameters names \c p, type \c t, value \c v, definitional height \c h \remark
    Theorems and definitions are essentially the same thing in Lean. The main difference is how the normalizer treats them.  The
    normalizer will only unfold a theorem if there is nothing else to be done when checking whether two terms are definitionally equal
    or not. */
lean_bool lean_decl_mk_thm(lean_name n, lean_list_name p, lean_expr t, lean_expr v, unsigned h, lean_decl * r, lean_exception * ex);
/** \brief Create a theorem with name \c n, universe parameters names \c p, type \c t, value \c v, definitional height \c h \remark
    Theorems and definitions are essentially the same thing in Lean. The main difference is how the normalizer treats them.  The
    normalizer will only unfold a theorem if there is nothing else to be done when checking whether two terms are definitionally equal
    or not.
    \remark The definitional height is computed using the information in the given environment. */
lean_bool lean_decl_mk_thm_with(lean_env e, lean_name n, lean_list_name p, lean_expr t, lean_expr v, lean_decl * r, lean_exception * ex);

/** \brief Delete/dispose the given declaration. */
void lean_decl_del(lean_decl d);
/** \brief Return the kind of the given declaration.
    \remark Return LEAN_DECL_CONST if d is null. */
lean_decl_kind lean_decl_get_kind(lean_decl d);

/** \brief Store in \c r the name the given declaration. */
lean_bool lean_decl_get_name(lean_decl d, lean_name * r, lean_exception * ex);
/** \brief Store in \c r the list of universe parameter names of the given declaration. */
lean_bool lean_decl_get_univ_params(lean_decl d, lean_list_name * r, lean_exception * ex);
/** \brief Store in \c r the type of the given declaration. */
lean_bool lean_decl_get_type(lean_decl d, lean_expr * r, lean_exception * ex);
/** \brief Store in \c r the value of the given theorem or definition.
    \pre lean_decl_get_kind(d) == LEAN_DECL_THM || lean_decl_get_kind(d) == LEAN_DECL_DEF
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_decl_get_value(lean_decl d, lean_expr * r, lean_exception * ex);
/** \brief Store in \c r the definitional height of the given theorem or definition.
    \pre lean_decl_get_kind(d) == LEAN_DECL_THM || lean_decl_get_kind(d) == LEAN_DECL_DEF
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_decl_get_height(lean_decl d, unsigned * r, lean_exception * ex);
/** \brief Store in \c r whether lazy unfolding is considered for the given definition.
    \pre lean_decl_get_kind(d) == LEAN_DECL_DEF
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_decl_get_conv_opt(lean_decl d, lean_bool * r, lean_exception * ex);

/** \brief Create a certified declaration by type checking the given declaration with respect to the given environment
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_decl_check(lean_env e, lean_decl d, lean_cert_decl * r, lean_exception * ex);
/** \brief Delete/dispose the given certified declaration. */
void lean_cert_decl_del(lean_cert_decl d);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
