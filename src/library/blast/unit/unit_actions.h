/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/action_result.h"

namespace lean {
namespace blast {
/* \brief The unit module handles lemmas of the form
   <tt>A_1 -> ... -> A_n -> B_1 \/ (B2 \/ ... \/ B_m)...)</tt>

   Whenever all but one of the literals is present as a hypothesis with
   the appropriate polarity, we instantiate and resolve as necessary
   to conclude a new literal.

   Remark: we assume that a pre-processing step will put lemmas
   into the above form when possible.
*/
action_result unit_propagate(unsigned hidx);

/* \brief We pre-process propositional lemmas to put them in the form
   expected by [unit_propagate]. In particular, we apply the following
   six transformations:

   1. A ∧ B → C ==> { A → B → C }
   2. A ∨ B → C ==> { A → C, B → C }
   3. A → B ∧ C ==> { A → C, A → C }
   4. A ↔ B ==> { (A → B) ∧ (B → A) }
   5. Push negations inside ∧ and ∨ (when using classical)
   6. ite A B C ==> { A → B, ¬ A → C }
*/
action_result unit_preprocess(unsigned hidx);

void initialize_unit_propagate();
void finalize_unit_propagate();

void initialize_unit_preprocess();
void finalize_unit_preprocess();

}}
