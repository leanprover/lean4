/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/action_result.h"

namespace lean {
namespace blast {
/* \brief Propagates lemmas of the form
   <tt>(A11 \/ ... \/ ...) -> ... -> (Am1 \/ ... \/ ...) -> (B1 /\ ... /\ ...)</tt>
   where each <tt>A</tt> and <tt>B</tt> can be any propositions, and can optionally
   be negated.

   If we can find one disjunct for every antecedent, we instantiate the lemma
   fully. On the other hand, if we can find one disjunct for all but one
   antecedents, and one fact that disproves the conjunctive conclusion,
   we conclude the negation of the missing disjunctive argument.

   Remark: conjunctions in the antecedents and disjunctions in the conclusion are
   both treated as monolithic propositions, so some pre-processing may be necessary.
*/
action_result unit_action(unsigned hidx);

void initialize_unit_action();
void finalize_unit_action();
}}
