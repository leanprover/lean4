/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
/* Type check 'e' using the given type context.
   It throws an exception in case of failure.

   This procedure is use to check the proof-term produced by tactics such as
   rewrite.
*/
void check(type_context_old & ctx, expr const & e);
void initialize_check();
void finalize_check();
}
