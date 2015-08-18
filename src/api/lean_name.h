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

LEAN_DEFINE_TYPE(lean_name);

/** \brief Create the anonymous name */
lean_bool lean_mk_anonymous_name(lean_name * r, lean_exception * e);
/** \brief Create the name <tt>pre.s</tt>
    \remark \c r must be disposed using #lean_del_name */
lean_bool lean_mk_str_name(lean_name pre, char const * s, lean_name * r, lean_exception * e);
/** \brief Create the name <tt>pre.i</tt>.
    \pre !lean_is_anonymous_name(pre)
    \remark \c r must be disposed using #lean_del_name */
lean_bool lean_mk_idx_name(lean_name pre, unsigned i, lean_name * r, lean_exception * e);
void lean_del_name(lean_name n);
/** \brief Return lean_true iff \c n is the anonymous */
lean_bool lean_is_anonymous_name(lean_name n);
/** \brief Return lean_true iff \c n is a name of the form <tt>pre.s</tt> where \c s is a string. */
lean_bool lean_is_str_name(lean_name n);
/** \brief Return lean_true iff \c n is a name of the form <tt>pre.i</tt> where \c i is an unsigned integer. */
lean_bool lean_is_idx_name(lean_name n);
/** \brief Return true iff the two given hierarchical names are equal */
lean_bool lean_name_eq(lean_name n1, lean_name n2);
/** \brief Return the prefix of the given name.
    \pre !lean_is_anonymous_name(n)
*/
lean_bool lean_get_name_prefix(lean_name n, lean_name * r, lean_exception * e);
/** \brief Store in \c r the suffix of the given name as a string.
    \pre lean_is_str_name(n)
    \remark \c r must be disposed using #lean_del_name
*/
lean_bool lean_get_name_str(lean_name n, char const ** r, lean_exception * e);
/** \brief Store in \c r the suffix of the given name as a unsigned integer.
    \pre lean_is_idx_name(n)
    \remark \c r must be deleted using #lean_del_string
*/
lean_bool lean_get_name_idx(lean_name n, unsigned * r, lean_exception * e);
/** \brief Store in \c r a string representation of the given hierarchical name.
    \remark \c r must be deleted using #lean_del_string
*/
lean_bool lean_name_to_string(lean_name n, char const **r, lean_exception * e);

#ifdef __cplusplus
};
#endif
#endif
