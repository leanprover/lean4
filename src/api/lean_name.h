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
    \remark \c r must be disposed using #lean_name_del
    \remark exceptions: LEAN_OTHER_EXCEPTION */
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
/** \brief Return true if \c n1 is smaller than \c n2 in the internal total order. */
lean_bool lean_name_lt(lean_name n1, lean_name n2);
/** \brief Return true if \c n1 is smaller than \c n2 in the internal total order.
    Similar to #lean_name_lt, but it is more efficient because it first compares
    the hashcodes associated with \c n1 and \c n2. */
lean_bool lean_name_quick_lt(lean_name n1, lean_name n2);
/** \brief Return the prefix of the given name.
    \pre !lean_name_is_anonymous(n)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_name_get_prefix(lean_name n, lean_name * r, lean_exception * ex);
/** \brief Store in \c r the suffix of the given name as a string.
    \pre lean_name_is_str(n)
    \remark \c r must be disposed using #lean_name_del
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_name_get_str(lean_name n, char const ** r, lean_exception * ex);
/** \brief Store in \c r the suffix of the given name as a unsigned integer.
    \pre lean_name_is_idx(n)
    \remark \c r must be deleted using #lean_string_del
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_name_get_idx(lean_name n, unsigned * r, lean_exception * ex);
/** \brief Store in \c r a string representation of the given hierarchical name.
    \remark \c r must be deleted using #lean_string_del */
lean_bool lean_name_to_string(lean_name n, char const **r, lean_exception * ex);

LEAN_DEFINE_TYPE(lean_list_name);

/** \brief Create the empty list of names */
lean_bool lean_list_name_mk_nil(lean_list_name * r, lean_exception * ex);
/** \brief Create the list <tt>h :: t</tt> */
lean_bool lean_list_name_mk_cons(lean_name h, lean_list_name t, lean_list_name * r, lean_exception * ex);
/** \brief Delete/dispose the given list of names */
void lean_list_name_del(lean_list_name l);
/** \brief Return true iff the list is a "cons" (i.e., it is not the nil list) */
lean_bool lean_list_name_is_cons(lean_list_name l);
/** \brief Return true iff the two given lists are equal */
lean_bool lean_list_name_eq(lean_list_name n1, lean_list_name n2);
/** \brief Store in \c r the head of the given list
    \pre lean_list_name_is_cons(l)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_list_name_head(lean_list_name l, lean_name * r, lean_exception * ex);
/** \brief Store in \c r the tail of the given list
    \pre lean_list_name_is_cons(l)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_list_name_tail(lean_list_name l, lean_list_name * r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
