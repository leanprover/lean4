/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/tactic/simp_result.h"
#include "library/app_builder.h"
#include "library/util.h"

namespace lean {

simp_result finalize(type_context_old & tctx, name const & rel, simp_result const & r) {
    if (r.has_proof()) return r;
    expr pf = mk_refl(tctx, rel, r.get_new());
    return simp_result(r.get_new(), pf);
}

simp_result join(type_context_old & tctx, name const & rel, simp_result const & r1, simp_result const & r2) {
    /* Assumes that both simp_results are with respect to the same relation */
    if (!r1.has_proof()) {
        return r2;
    } else if (!r2.has_proof()) {
        lean_assert(r1.has_proof());
        return simp_result(r2.get_new(), r1.get_proof());
    } else {
        /* If they both have proofs, we need to glue them together with transitivity. */
        lean_assert(r1.has_proof() && r2.has_proof());
        expr trans = mk_trans(tctx, rel, r1.get_proof(), r2.get_proof());
        return simp_result(r2.get_new(), trans);
    }
}

simp_result finalize_eq(abstract_type_context & tctx, simp_result const & r) {
    if (r.has_proof()) return r;
    expr pf = mk_eq_refl(tctx, r.get_new());
    return simp_result(r.get_new(), pf);
}

simp_result join_eq(abstract_type_context & tctx, simp_result const & r1, simp_result const & r2) {
    if (!r1.has_proof()) {
        return r2;
    } else if (!r2.has_proof()) {
        lean_assert(r1.has_proof());
        return simp_result(r2.get_new(), r1.get_proof());
    } else {
        lean_assert(r1.has_proof() && r2.has_proof());
        expr trans = mk_eq_trans(tctx, r1.get_proof(), r2.get_proof());
        return simp_result(r2.get_new(), trans);
    }
}

}
