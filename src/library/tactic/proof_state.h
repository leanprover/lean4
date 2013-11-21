/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/justification_builder.h"

namespace lean {
class proof_state {
    list<std::pair<name, goal>> m_goals;
    metavar_env                 m_menv;
    proof_builder               m_proof_builder;
    justification_builder       m_justification_builder;
public:
};
}
