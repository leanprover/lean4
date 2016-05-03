/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Inline functions definitions of the form g x_1 ... x_n := f y_1 ... y_m,
    where y_i's are pairwise distinct variables (or constants).
    g is a variable or constant.

    This procedure also simplifies projection applications.

    Example: this procedure reduces (@add nat nat_has_add a b) into (nat.add a b). */
expr inline_simple_definitions(environment const & env, expr const & e);
}
