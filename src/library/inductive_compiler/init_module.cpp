/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/trace.h"
#include "library/inductive_compiler/init_module.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/mutual.h"
#include "library/inductive_compiler/nested.h"
#include "library/inductive_compiler/add_decl.h"

namespace lean {
void initialize_inductive_compiler_module() {
    register_trace_class(name({"inductive_compiler"}));
    register_trace_class(name({"debug", "inductive_compiler"}));
    initialize_inductive_compiler_add_decl();
    initialize_inductive_compiler();
    initialize_inductive_compiler_ginductive();
    initialize_inductive_compiler_basic();
    initialize_inductive_compiler_mutual();
    initialize_inductive_compiler_nested();
}

void finalize_inductive_compiler_module() {
    finalize_inductive_compiler_nested();
    finalize_inductive_compiler_mutual();
    finalize_inductive_compiler_basic();
    finalize_inductive_compiler_ginductive();
    finalize_inductive_compiler();
    finalize_inductive_compiler_add_decl();
}
}
