/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "util/numerics/mpq.h"

namespace lean {

expr mk_mpq_macro(mpq const & q, expr const & type);

bool is_mpq_macro(expr const & e);
bool is_mpq_macro(expr const & e, mpq & q);

void initialize_mpq_macro();
void finalize_mpq_macro();
}
