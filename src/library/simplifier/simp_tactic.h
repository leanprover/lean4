/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/tactic/location.h"

namespace lean {
/** \brief Create a simp tactic expression where
    - ls is a collection of pre-terms representing additional lemmas that should be used as rewriting rules.
    - ns is a collection of namespaces that should provide rewriting rules for this tactic.
    - ex is a collection of global rewriting rules that should be excluded.
    - pre_tac (if provided) is a tactic used to discharge assumptions in conditional rewriting rules.
    - loc is the scope of the tactic (i.e., which hypothesis and/or conclusion will be simplified).
*/
expr mk_simp_tactic_expr(buffer<expr> const & ls, buffer<name> const & ns, buffer<name> const & ex,
                         optional<expr> const & pre_tac, location const & loc);

void initialize_simp_tactic();
void finalize_simp_tactic();
}
