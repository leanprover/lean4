/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/goal.h"

namespace lean {
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g);
void initialize_blast();
void finalize_blast();
}
