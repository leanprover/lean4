/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/compiler/procedure.h"
namespace lean {
/* Create new 0-ary procedures for nested values.
   We say a value is a nested closed application or non 0-ary macro.

   Recall that the bytecode VM caches the value of 0-ary procedures.
   So, by creating 0-ary procedures, we will cache their values during execution. */
void extract_values(environment const & env, abstract_context_cache & cache, name const & prefix, buffer<procedure> & procs);
}
