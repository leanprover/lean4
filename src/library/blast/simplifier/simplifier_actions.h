/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/hypothesis.h"
#include "library/blast/action_result.h"
namespace lean {
namespace blast {
action_result simplify_hypothesis_action(hypothesis_idx hidx);
action_result simplify_target_action();

void initialize_simplifier_actions();
void finalize_simplifier_actions();
}}
