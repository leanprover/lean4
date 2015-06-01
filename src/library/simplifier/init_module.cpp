/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/simplifier/rewrite_rule_set.h"

namespace lean {
void initialize_simplifier_module() {
    initialize_rewrite_rule_set();
}
void finalize_simplifier_module() {
    finalize_rewrite_rule_set();
}
}
