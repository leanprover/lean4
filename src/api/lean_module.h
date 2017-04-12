/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_MODULE_H
#define _LEAN_MODULE_H

#ifdef __cplusplus
extern "C" {
#endif

/**
   \defgroup capi C API
*/
/*@{*/

/**
   @name Module API
*/
/*@{*/

/** \brief Import the given modules (i.e., pre-compiled .olean files)
    \remark exceptions: LEAN_KERNEL_EXCEPTION, LEAN_OTHER_EXCEPTION */
lean_bool lean_env_import(lean_env env, lean_ios ios, lean_list_name modules, lean_env * r, lean_exception * ex);

/** \brief Export to the given file name the declarations added to the environment
    \remark exceptions: LEAN_OTHER_EXCEPTION */
lean_bool lean_env_export(lean_env env, char const * fname, lean_exception * ex);

/*@}*/
/*@}*/

#ifdef __cplusplus
};
#endif
#endif
