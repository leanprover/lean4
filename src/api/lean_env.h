/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_ENV_H
#define _LEAN_ENV_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Environment API
*/
/*@{*/

/** \brief Create a standard environment (i.e., proof irrelevant, and containing an impredicative Prop) with trust level \c t.
    If the trust level is 0, then all imported modules are retype-checked, and declarations containing macros are rejected. */
lean_bool lean_env_mk_std(unsigned t, lean_env * r, lean_exception * ex);

/** Trust all macros implemented in Lean, and do no retype-check imported modules */
#define LEAN_TRUST_HIGH 100000

/** \brief Create a new environment by adding the given certified declaration \c d to the environment \c e.
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_env_add(lean_env e, lean_cert_decl d, lean_env * r, lean_exception * ex);
/** \brief Replace the axiom with the name of the given certified theorem \c d with \c d.
    This procedure throws an exception if:
    - The theorem was certified in an environment which is not an ancestor of \c e.
    - The environment does not contain an axiom with the given name.
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_env_replace(lean_env e, lean_cert_decl d, lean_env * r, lean_exception * ex);

/** \brief Delete/dispose the given environment. */
void lean_env_del(lean_env e);

/** \brief Return the trust level of the given environment */
unsigned lean_env_trust_level(lean_env e);

/** \brief Return true iff \c e contains a declaration with name \c n. */
lean_bool lean_env_contains_decl(lean_env e, lean_name n);
/** \brief Store in \c d the declaration with name \c n in \c e.
    \remark exceptions: LEAN_KERNEL_EXCEPTION */
lean_bool lean_env_get_decl(lean_env e, lean_name n, lean_decl * d, lean_exception * ex);

/** \brief Return true when \c e1 is a descendant of \c e2, that is, \c e1 was created by adding declarations to \c e2. */
lean_bool lean_env_is_descendant(lean_env e1, lean_env e2);
/** \brief Return a new environment, where its "history" has been truncated/forgotten.
    That is, <tt>is_descendant(r, e2)</tt> will return false for any environment \c e2 that
    is not pointer equal to the result. */
lean_bool lean_env_forget(lean_env e, lean_env * r, lean_exception * ex);

/** \brief Execute \c f for each declaration in \c env.
    \remark Every declaration passed to \c f must be disposed using \c lean_decl_del. */
lean_bool lean_env_for_each_decl(lean_env e, void (*f)(lean_decl), lean_exception * ex);
/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
