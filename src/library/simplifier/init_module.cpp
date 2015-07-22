/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/simplifier/simp_rule_set.h"
#include "library/simplifier/simp_tactic.h"

namespace lean {
void initialize_simplifier_module() {
    initialize_simp_rule_set();
    initialize_simp_tactic();
}
void finalize_simplifier_module() {
    finalize_simp_tactic();
    finalize_simp_rule_set();
}
}
