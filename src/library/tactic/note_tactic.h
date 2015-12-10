/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_note_tactic_expr(name const &id, expr const &e);
void initialize_note_tactic();
void finalize_note_tactic();
}
