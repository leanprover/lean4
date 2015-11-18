/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/action_result.h"
namespace lean {
namespace blast {
/** \brief Introduce upto \c max hypotheses.
    Return failed if there is nothing to introduce, that is, target is not a Pi-type.
    \remark if max == 0, and it returns new_branch. */
action_result intros_action(unsigned max);
/** \brief Keep introducing until target is not a Pi-type. */
action_result intros_action();
}}
