/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/blast/blast.h"
#include "library/blast/action_result.h"
#include "library/blast/forward/forward_actions.h"
#include "library/blast/proof_expr.h"
#include "library/blast/choice_point.h"
#include "library/blast/hypothesis.h"
#include "library/blast/util.h"
#include "library/expr_lt.h"
#include "library/head_map.h"

namespace lean {
namespace blast {

action_result qfc_action(list<gexpr> const & lemmas) {
    return action_result::failed();
}

}}
