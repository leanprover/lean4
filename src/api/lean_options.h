/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_OPTIONS_H
#define _LEAN_OPTIONS_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Configuration options API

   A configuration options is essentially a mapping from names to values.
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_options);

/** \brief Create an empty configuration options object. */
lean_bool lean_options_mk_empty(lean_options * r, lean_exception * ex);
/** \brief r := o[n := v]
    \remark \c r must be disposed using #lean_options_del */
lean_bool lean_options_set_bool(lean_options o, lean_name n, lean_bool v, lean_options * r, lean_exception * ex);
/** \brief r := o[n := v]
    \remark \c r must be disposed using #lean_options_del */
lean_bool lean_options_set_int(lean_options o, lean_name n, int v, lean_options * r, lean_exception * ex);
/** \brief r := o[n := v]
    \remark \c r must be disposed using #lean_options_del */
lean_bool lean_options_set_unsigned(lean_options o, lean_name n, unsigned v, lean_options * r, lean_exception * ex);
/** \brief r := o[n := v]
    \remark \c r must be disposed using #lean_options_del */
lean_bool lean_options_set_double(lean_options o, lean_name n, double v, lean_options * r, lean_exception * ex);
/** \brief r := o[n := v]
    \remark \c r must be disposed using #lean_options_del */
lean_bool lean_options_set_string(lean_options o, lean_name n, char const * v, lean_options * r, lean_exception * ex);
/** \brief Combine the options o1 and o2 and store the result in \c r.
    \remark The assignments in o2 overrides the ones in o1.
    \remark \c r must be disposed using #lean_options_del */
lean_bool lean_options_join(lean_options o1, lean_options o2, lean_options * r, lean_exception * ex);

/** \brief Delete/dispose the given options object.  */
void lean_options_del(lean_options o);

/** \brief Store in \c r a string representation of the given options object.
    \remark \c r must be deleted using #lean_string_del
*/
lean_bool lean_options_to_string(lean_options o, char const ** r, lean_exception * ex);
/** \brief Return true iff the two given options object are equal. */
lean_bool lean_options_eq(lean_options o1, lean_options o2);
/** \brief Return true iff the given options object is empty. */
lean_bool lean_options_empty(lean_options o);
/** \brief Return true iff the given options object contains the entry \c n. */
lean_bool lean_options_contains(lean_options o, lean_name n);

/** \brief Store in \c r the value assigned to \c n in the options \c o.
    \pre lean_options_contains(o, n)
    \remark If the value associated with \c n is not a Boolean, the result is lean_false
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_options_get_bool(lean_options o, lean_name n, lean_bool * r, lean_exception * ex);
/** \brief Store in \c r the value assigned to \c n in the options \c o.
    \pre lean_options_contains(o, n)
    \remark If the value associated with \c n is not a numeric value, the result is 0
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_options_get_int(lean_options o, lean_name n, int * r, lean_exception * ex);
/** \brief Store in \c r the value assigned to \c n in the options \c o.
    \pre lean_options_contains(o, n)
    \remark If the value associated with \c n is not a numeric value, the result is 0
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_options_get_unsigned(lean_options o, lean_name n, unsigned * r, lean_exception * ex);
/** \brief Store in \c r the value assigned to \c n in the options \c o.
    \pre lean_options_contains(o, n)
    \remark If the value associated with \c n is not a double, the result is 0.0
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_options_get_double(lean_options o, lean_name n, double * r, lean_exception * ex);
/** \brief Store in \c r the value assigned to \c n in the options \c o.
    \pre lean_options_contains(o, n)
    \remark If the value associated with \c n is not a double, the result is the empty string ""
    \remark \c r must be deleted using #lean_string_del.
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_options_get_string(lean_options o, lean_name n, char const ** r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
