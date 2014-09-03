/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"

namespace lean {
/** \brief Given an expression \c e, return the number of arguments expected arguments.

    \remark This function computes the type of \c e, and then counts the number of nested
    Pi's. Weak-head-normal-forms are computed for the type of \c e.
    \remark The type and whnf are computed using \c tc.
*/
unsigned get_expect_num_args(type_checker & tc, expr e);
}
