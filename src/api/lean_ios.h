/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_IOS_H
#define _LEAN_IOS_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name IO state API
*/
/*@{*/

LEAN_DEFINE_TYPE(lean_ios);

/** \brief Create IO state object that sends the regular and diagnostic output to standard out and standard error */
lean_bool lean_ios_mk_std(lean_options o, lean_ios * r, lean_exception * ex);

/** \brief Create IO state object that sends the regular and diagnostic output to string buffers. */
lean_bool lean_ios_mk_buffered(lean_options o, lean_ios * r, lean_exception * ex);

/** \brief Delete IO state object. */
void lean_ios_del(lean_ios ios);

/** \brief Return true iff it is standard IO state (i.e., it was created using #lean_ios_mk_std */
lean_bool lean_ios_is_std(lean_ios ios);

/** \brief Update the set of configurations options in the given IO state object */
lean_bool lean_ios_set_options(lean_ios ios, lean_options o, lean_exception * ex);

/** \brief Store in \c r the set of configuration options associated with the given IO state object. */
lean_bool lean_ios_get_options(lean_ios ios, lean_options * r, lean_exception * ex);

/** \brief Store in \c r the content of the regular output stream.
    \pre !lean_ios_is_std(ios)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_ios_get_regular(lean_ios ios, char const ** r, lean_exception * ex);

/** \brief Store in \c r the content of the diagnostic output stream.
    \pre !lean_ios_is_std(ios)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_ios_get_diagnostic(lean_ios ios, char const ** r, lean_exception * ex);

/** \brief Reset the regular output stream.
    \pre !lean_ios_is_std(ios)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_ios_reset_regular(lean_ios ios, lean_exception * ex);

/** \brief Reset the diagnostic output stream.
    \pre !lean_ios_is_std(ios)
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_ios_reset_diagnostic(lean_ios ios, lean_exception * ex);

/** \brief Store in \c r a pretty printed representation of \c e */
lean_bool lean_expr_to_pp_string(lean_env env, lean_ios ios, lean_expr e, char const ** r, lean_exception * ex);

/** \brief Store in \c r a pretty printed representation of the exception \c e */
lean_bool lean_exception_to_pp_string(lean_env env, lean_ios ios, lean_exception e, char const ** r, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
