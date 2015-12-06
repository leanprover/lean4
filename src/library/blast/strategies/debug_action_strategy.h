/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/strategy.h"
namespace lean {
namespace blast {
/* \brief Create minimalistic strategies for testing the given action.
   These strategies apply basic actions (e.g., intros and assumption) and the given action. */
strategy mk_debug_action_strategy(std::function<action_result()> const & a);
strategy mk_debug_pre_action_strategy(std::function<action_result(hypothesis_idx)> const & a);
strategy mk_debug_post_action_strategy(std::function<action_result(hypothesis_idx)> const & a);
strategy mk_debug_action_strategy(std::function<action_result(hypothesis_idx)> const & pre,
                                  std::function<action_result(hypothesis_idx)> const & post,
                                  std::function<action_result()> const & next);
}}
