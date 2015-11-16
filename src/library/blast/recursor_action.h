/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/action_result.h"
#include "library/blast/hypothesis.h"
namespace lean {
namespace blast {
/** \brief Return the name of the recursor that can be used with the given hypothesis */
optional<name> is_recursor_action_target(hypothesis_idx hidx);

/** \brief Return the number of minor premises of the given recursor */
unsigned get_num_minor_premises(name const & R);
bool is_recursive_recursor(name const & R);

action_result recursor_action(hypothesis_idx hidx, name const & R);
action_result recursor_action(hypothesis_idx hidx);
}}
