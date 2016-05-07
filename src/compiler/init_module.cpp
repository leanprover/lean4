/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "compiler/preprocess_rec.h"
#include "compiler/fresh_constant.h"
#include "compiler/comp_irrelevant.h"
#include "compiler/inliner.h"
#include "compiler/rec_fn_macro.h"
#include "compiler/erase_irrelevant.h"

namespace lean {
void initialize_compiler_module() {
    initialize_preprocess_rec();
    initialize_fresh_constant();
    initialize_comp_irrelevant();
    initialize_inliner();
    initialize_rec_fn_macro();
    initialize_erase_irrelevant();
}
void finalize_compiler_module() {
    finalize_erase_irrelevant();
    finalize_rec_fn_macro();
    finalize_inliner();
    finalize_comp_irrelevant();
    finalize_preprocess_rec();
    finalize_fresh_constant();
}
}
