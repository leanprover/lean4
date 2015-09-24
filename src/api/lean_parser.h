/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_PARSER_H
#define _LEAN_PARSER_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Parser API
*/
/*@{*/

/** \brief Parse the file \c fname using \c env and \c ios.
    Store the updated environment and ios at \c new_env and \c new_ios.
    \remark We return a new ios object because Lean has commands for updating configuration options.
    \remark exceptions: LEAN_KERNEL_EXCEPTION, LEAN_PARSER_EXCEPTION, LEAN_UNIFIER_EXCEPTION, LEAN_TACTIC_EXCEPTION, LEAN_OTHER_EXCEPTION */
lean_bool lean_parse_file(lean_env env, lean_ios ios, char const * fname, lean_env * new_env, lean_ios * new_ios, lean_exception * ex);

/** \brief Parse the commands in the string \c str using \c env and \c ios.
    Store the updated environment and ios at \c new_env and \c new_ios.
    \remark We return a new ios object because Lean has commands for updating configuration options.
    \remark exceptions: LEAN_KERNEL_EXCEPTION, LEAN_PARSER_EXCEPTION, LEAN_UNIFIER_EXCEPTION, LEAN_TACTIC_EXCEPTION, LEAN_OTHER_EXCEPTION */
lean_bool lean_parse_commands(lean_env env, lean_ios ios, char const * str, lean_env * new_env, lean_ios * new_ios, lean_exception * ex);

/** \brief Parse (and elaborate) the expression in the string \c str using \c env and \c ios.
    Store the elaborated expression in \c new_expr, and automatically generated universe parameters in \c new_ps.
    \remark exceptions: LEAN_KERNEL_EXCEPTION, LEAN_PARSER_EXCEPTION, LEAN_UNIFIER_EXCEPTION, LEAN_TACTIC_EXCEPTION, LEAN_OTHER_EXCEPTION */
lean_bool lean_parse_expr(lean_env env, lean_ios ios, char const * str, lean_expr * new_expr, lean_list_name * new_ps, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
