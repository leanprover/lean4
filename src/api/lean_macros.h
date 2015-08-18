/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifndef _LEAN_MACROS_H
#define _LEAN_MACROS_H

#ifndef LEAN_API
  #ifdef __GNUC__
  #define LEAN_API __attribute__ ((visibility ("default")))
  #else
  #define LEAN_API
  #endif
#endif

#ifndef LEAN_DEFINE_TYPE
#define LEAN_DEFINE_TYPE(T) typedef struct _ ## T *T
#endif

#ifndef LEAN_DEFINE_VOID
#define LEAN_DEFINE_VOID(T) typedef void* T
#endif

#endif
