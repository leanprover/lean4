/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_STRING_H
#define _LEAN_STRING_H
#ifdef __cplusplus
extern "C" {
#endif

/** \brief Delete a string allocated by Lean */
void lean_string_del(char const * s);

#ifdef __cplusplus
};
#endif
#endif
