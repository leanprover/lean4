/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "library/tactic/elaborator_exception.h"
#include "library/vm/interaction_state.h"

namespace lean {
elaborator_exception unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
elaborator_exception unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);

format mk_tactic_error_msg(tactic_state const & ts, format const & fmt);
}
