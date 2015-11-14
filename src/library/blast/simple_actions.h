/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
namespace blast {
optional<expr> assumption_action();
/** \brief Apply assumption and contradiction actions using the given hypothesis.
    \remark This action is supposed to be applied when a hypothesis is activated. */
optional<expr> assumption_contradiction_actions(hypothesis_idx hidx);
/** \brief Solve trivial targets (e.g., true, a = a, a <-> a, etc). */
optional<expr> trivial_action();
}}
