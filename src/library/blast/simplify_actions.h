/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/hypothesis.h"
namespace lean {
namespace blast {
optional<hypothesis_idx> simplify_hypothesis_action(hypothesis_idx hidx);
bool add_simp_rule_action(hypothesis_idx hidx);
action_result simplify_target_action();
}}
