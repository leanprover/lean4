/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/compiler/preprocess.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/inliner.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/vm_compiler.h"

namespace lean {
void initialize_compiler_module() {
    initialize_preprocess();
    initialize_nat_value();
    initialize_comp_irrelevant();
    initialize_inliner();
    initialize_rec_fn_macro();
    initialize_erase_irrelevant();
    initialize_simp_inductive();
    initialize_vm_compiler();
}

void finalize_compiler_module() {
    finalize_vm_compiler();
    finalize_simp_inductive();
    finalize_erase_irrelevant();
    finalize_rec_fn_macro();
    finalize_inliner();
    finalize_comp_irrelevant();
    finalize_nat_value();
    finalize_preprocess();
}
}
