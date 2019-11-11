/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/structural_rec.h"
#include "library/equations_compiler/wf_rec.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/pack_mutual.h"
#include "library/equations_compiler/compiler.h"

namespace lean{
void initialize_equations_compiler_module() {
    initialize_eqn_compiler_util();
    initialize_equations();
    initialize_pack_mutual();
    initialize_structural_rec();
    initialize_wf_rec();
    initialize_elim_match();
    initialize_eqn_compiler();
}

void finalize_equations_compiler_module() {
    finalize_eqn_compiler();
    finalize_elim_match();
    finalize_structural_rec();
    finalize_wf_rec();
    finalize_pack_mutual();
    finalize_equations();
    finalize_eqn_compiler_util();
}
}
