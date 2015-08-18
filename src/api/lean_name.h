/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_NAME_H
#define _LEAN_NAME_H

#ifdef __cplusplus
extern "C" {
#endif
/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Hierarchical names API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_name);

/** \brief Create the anonymous name */
lean_bool lean_name_mk_anonymous(lean_name * r, lean_exception * ex);
/** \brief Create the name <tt>pre.s</tt>
    \remark \c r must be disposed using #lean_name_del */
lean_bool lean_name_mk_str(lean_name pre, char const * s, lean_name * r, lean_exception * ex);
/** \brief Create the name <tt>pre.i</tt>.
    \pre !lean_name_is_anonymous(pre)
    \remark \c r must be disposed using #lean_name_del */
lean_bool lean_name_mk_idx(lean_name pre, unsigned i, lean_name * r, lean_exception * ex);
/** \brief Delete/dispose the given hierarchical name */
void lean_name_del(lean_name n);
/** \brief Return lean_true iff \c n is the anonymous */
lean_bool lean_name_is_anonymous(lean_name n);
/** \brief Return lean_true iff \c n is a name of the form <tt>pre.s</tt> where \c s is a string. */
lean_bool lean_name_is_str(lean_name n);
/** \brief Return lean_true iff \c n is a name of the form <tt>pre.i</tt> where \c i is an unsigned integer. */
lean_bool lean_name_is_idx(lean_name n);
/** \brief Return true iff the two given hierarchical names are equal */
lean_bool lean_name_eq(lean_name n1, lean_name n2);
/** \brief Return the prefix of the given name.
    \pre !lean_name_is_anonymous(n)
*/
lean_bool lean_name_get_prefix(lean_name n, lean_name * r, lean_exception * ex);
/** \brief Store in \c r the suffix of the given name as a string.
    \pre lean_name_is_str(n)
    \remark \c r must be disposed using #lean_name_del
*/
lean_bool lean_name_get_str(lean_name n, char const ** r, lean_exception * ex);
/** \brief Store in \c r the suffix of the given name as a unsigned integer.
    \pre lean_name_is_idx(n)
    \remark \c r must be deleted using #lean_string_del
*/
lean_bool lean_name_get_idx(lean_name n, unsigned * r, lean_exception * ex);
/** \brief Store in \c r a string representation of the given hierarchical name.
    \remark \c r must be deleted using #lean_string_del
*/
lean_bool lean_name_to_string(lean_name n, char const **r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
