/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/strategy.h"
namespace lean {
namespace blast {
strategy mk_backward_strategy();
strategy mk_backward_strategy(char const * n);

/* Extensible backward chaining strategy
   - n         : name of the new strategy
   - pre       : action to be executed before given hypothesis is activated
   - post      : action to be executed after given hypothesis is activated
   - pre_next  : action to be executed before backward chaining,
                 i.e., backward chaining will only be considered when this action fails
   - post_next : action to be executed after backward chaining cannot be applied anymore
                 because maximum number of rounds has been reached or no [intro] lemma
                 is applicable
 */
strategy mk_xbackward_strategy(char const * n,
                               std::function<action_result(hypothesis_idx)> const & pre,
                               std::function<action_result(hypothesis_idx)> const & post,
                               std::function<action_result()> const & pre_next,
                               std::function<action_result()> const & post_next);

void initialize_backward_strategy();
void finalize_backward_strategy();
}}
