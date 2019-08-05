/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
namespace lean {
expr clear(metavar_context & mctx, expr const & mvar, expr const & H);
void initialize_clear_tactic();
void finalize_clear_tactic();
}
