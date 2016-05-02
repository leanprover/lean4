/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "compiler/preprocess_rec.h"
#include "compiler/fresh_constant.h"
#include "compiler/comp_irrelevant.h"

namespace lean{
void initialize_compiler_module() {
    initialize_preprocess_rec();
    initialize_fresh_constant();
    initialize_comp_irrelevant();
}
void finalize_compiler_module() {
    finalize_comp_irrelevant();
    finalize_preprocess_rec();
    finalize_fresh_constant();
}
}
