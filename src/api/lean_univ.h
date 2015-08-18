/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_UNIV_H
#define _LEAN_UNIV_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Universe API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_univ);

typedef enum {
    LEAN_UNIV_ZERO,
    LEAN_UNIV_SUCC,
    LEAN_UNIV_MAX,
    LEAN_UNIV_IMAX,
    LEAN_UNIV_PARAM,
    LEAN_UNIV_GLOBAL,
    LEAN_UNIV_META
} lean_univ_kind;

/** \brief Create the base universe zero */
lean_bool lean_univ_mk_zero(lean_univ * r, lean_exception * ex);
/** \brief Create the successor universe */
lean_bool lean_univ_mk_succ(lean_univ u, lean_univ * r, lean_exception * ex);
/** \brief r := max(u1, u2) */
lean_bool lean_univ_mk_max(lean_univ u1, lean_univ u2, lean_univ * r, lean_exception * ex);
/** \brief r := imax(u1, u2) */
lean_bool lean_univ_mk_imax(lean_univ u1, lean_univ u2, lean_univ * r, lean_exception * ex);
/** \brief Create a universe parameter with the given name. */
lean_bool lean_univ_mk_param(lean_name n, lean_univ * r, lean_exception * ex);
/** \brief Create a reference to a global universe with the given name. */
lean_bool lean_univ_mk_global(lean_name n, lean_univ * r, lean_exception * ex);
/** \brief Create a universe meta-variable with the given name. */
lean_bool lean_univ_mk_meta(lean_name n, lean_univ * r, lean_exception * ex);

/** \brief Store in \c r a string representation of the given universe object.
    \remark \c r must be deleted using #lean_string_del */
lean_bool lean_univ_to_string(lean_univ u, char const ** r, lean_exception * ex);

/** \brief Similar to \c lean_univ_to_string, but uses pretty printing options in \c o,
    when converting objection into a string. */
lean_bool lean_univ_to_string_using(lean_univ u, lean_options o, char const ** r, lean_exception * ex);
/** \brief Delete/dispose the given universe object. */
void lean_univ_del(lean_univ u);
/** \brief Return the kind of the given universe.
    \remark Return LEAN_UNIV_ZERO if u is null. */
lean_univ_kind lean_univ_get_kind(lean_univ u);

/** \brief Store \c lean_true in \c r iff the two given universe object are equal. */
lean_bool lean_univ_eq(lean_univ u1, lean_univ u2, lean_bool * r, lean_exception * ex);
/** \brief If \c r contains \c lean_true, then forall assignments \c A that assigns all parameters,
    globals and metavariables occuring in \c u1 and \c u2, we have that the
    universe level u1[A] is bigger or equal to u2[A]. */
lean_bool lean_univ_geq(lean_univ u1, lean_univ u2, lean_bool * r, lean_exception * ex);

/** \brief Store the predecessor universe of \c u in \c r.
    \pre lean_univ_get_kind(u) == LEAN_UNIV_SUCC
*/
lean_bool lean_univ_get_pred(lean_univ u, lean_univ * r, lean_exception * ex);
/** \brief Store the left-hand-side of the max/imax universe \c u in \c r.
    \pre lean_univ_get_kind(u) == LEAN_UNIV_MAX || lean_univ_get_kind(u) == LEAN_UNIV_IMAX
*/

lean_bool lean_univ_get_max_lhs(lean_univ u, lean_univ * r, lean_exception * ex);
/** \brief Store the right-hand-side of the max/imax universe \c u in \c r.
    \pre lean_univ_get_kind(u) == LEAN_UNIV_MAX || lean_univ_get_kind(u) == LEAN_UNIV_IMAX
*/
lean_bool lean_univ_get_max_rhs(lean_univ u, lean_univ * r, lean_exception * ex);
/** \brief Store the name of the given universe in \c r.
    \pre lean_univ_get_kind(u) == LEAN_UNIV_PARAM ||
         lean_univ_get_kind(u) == LEAN_UNIV_GLOBAL ||
         lean_univ_get_kind(u) == LEAN_UNIV_META
*/
lean_bool lean_univ_get_name(lean_univ u, lean_name * r, lean_exception * ex);
/** \brief Store in \c r the normal for of the given universe */
lean_bool lean_univ_normalize(lean_univ u, lean_univ * r, lean_exception * ex);

/** \brief Instantiate the universe parameters names <tt>ns[i]</tt> with <tt>us[i]</tt> in \c u,
    and store the result in \c r.
    \remark \c ns and \c us are arrays of names and universes, and both have size \c sz.
*/
lean_bool lean_univ_instantiate(lean_univ u, unsigned sz, lean_name const * ns, lean_univ const * us,
                                lean_univ * r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
