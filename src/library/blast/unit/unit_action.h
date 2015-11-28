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
   the appropriate polarity, we instantiate and resolve and necessary
   to conclude a new literal.

   Remark: we assume that a pre-processing step will put lemmas
   into the above form when possible.
*/
action_result unit_action(unsigned hidx);

void initialize_unit_action();
void finalize_unit_action();
}}
