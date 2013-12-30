/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/io_state.h"
#include "library/basic_thms.h"

namespace lean {

MK_CONSTANT(trivial,            name("Trivial"));
MK_CONSTANT(true_neq_false,     name("TrueNeFalse"));
MK_CONSTANT(false_elim_fn,      name("FalseElim"));
MK_CONSTANT(absurd_fn,          name("Absurd"));
MK_CONSTANT(em_fn,              name("EM"));
MK_CONSTANT(double_neg_fn,      name("DoubleNeg"));
MK_CONSTANT(double_neg_elim_fn, name("DoubleNegElim"));
MK_CONSTANT(mt_fn,              name("MT"));
MK_CONSTANT(contrapos_fn,       name("Contrapos"));
MK_CONSTANT(false_imp_any_fn,   name("FalseImpAny"));
MK_CONSTANT(absurd_elim_fn,     name("AbsurdElim"));
MK_CONSTANT(eq_mp_fn,           name("EqMP"));
MK_CONSTANT(not_imp1_fn,        name("NotImp1"));
MK_CONSTANT(not_imp2_fn,        name("NotImp2"));
MK_CONSTANT(conj_fn,            name("Conj"));
MK_CONSTANT(conjunct1_fn,       name("Conjunct1"));
MK_CONSTANT(conjunct2_fn,       name("Conjunct2"));
MK_CONSTANT(disj1_fn,           name("Disj1"));
MK_CONSTANT(disj2_fn,           name("Disj2"));
MK_CONSTANT(disj_cases_fn,      name("DisjCases"));
MK_CONSTANT(refute_fn,          name("Refute"));
MK_CONSTANT(symm_fn,            name("Symm"));
MK_CONSTANT(trans_fn,           name("Trans"));
MK_CONSTANT(congr1_fn,          name("Congr1"));
MK_CONSTANT(congr2_fn,          name("Congr2"));
MK_CONSTANT(congr_fn,           name("Congr"));
MK_CONSTANT(eqt_elim_fn,        name("EqTElim"));
MK_CONSTANT(eqt_intro_fn,       name("EqTIntro"));
MK_CONSTANT(forall_elim_fn,     name("ForallElim"));
MK_CONSTANT(forall_intro_fn,    name("ForallIntro"));
MK_CONSTANT(exists_elim_fn,     name("ExistsElim"));
MK_CONSTANT(exists_intro_fn,    name("ExistsIntro"));

void import_basic_thms(environment const & env) {
    io_state ios;
    env->import("basic", ios);
}
}
