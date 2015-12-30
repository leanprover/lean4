/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/strategy.h"
namespace lean {
namespace blast {
/* \brief Create minimalistic strategies for testing and executing actions.
   These strategies apply basic actions (e.g., intros and assumption) and the given action. */
strategy mk_action_strategy(char const * name,
                            std::function<action_result()> const & a);
strategy mk_pre_action_strategy(char const * name,
                                std::function<action_result(hypothesis_idx)> const & a);
strategy mk_action_strategy(char const * name,
                            std::function<action_result(hypothesis_idx)> const & a);
strategy mk_action_strategy(char const * name,
                            std::function<action_result(hypothesis_idx)> const & pre,
                            std::function<action_result(hypothesis_idx)> const & post,
                            std::function<action_result()> const & next);
}}
