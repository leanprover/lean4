/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_delayed_cc_eq_proof(expr const & e1, expr const & e2);
expr mark_cc_theory_proof(expr const & pr);
expr get_cc_theory_proof_arg(expr const & pr);
bool is_cc_theory_proof(expr const & e);

class congruence_closure;
expr expand_delayed_cc_proofs(congruence_closure const & cc, expr const & e);

void initialize_smt_util();
void finalize_smt_util();
}
