/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/tmp_type_context.h"
#include "library/defeq_simp_lemmas.h"

namespace lean {

expr defeq_simplify(tmp_type_context_pool & tmp_tctx_pool, options const & o, defeq_simp_lemmas const & simp_lemmas, expr const & e);

void initialize_defeq_simplifier();
void finalize_defeq_simplifier();

}
