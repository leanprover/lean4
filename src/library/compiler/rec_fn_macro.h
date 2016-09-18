/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/* \brief Recursive macro is essentially an annotation for the code generator.
   It allows the code generator preprocessing steps to use arbitrary recursion.
   To make sure we can typecheck the result of the preprocessing steps,
   we must provide the type of the function. */
expr mk_rec_fn_macro(name const & fn_name, expr const & type);

bool is_rec_fn_macro(expr const & e);
name const & get_rec_fn_name(expr const & e);
expr const & get_rec_fn_type(expr const & e);

void initialize_rec_fn_macro();
void finalize_rec_fn_macro();
}
