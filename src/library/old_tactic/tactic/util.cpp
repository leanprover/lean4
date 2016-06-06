/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/aliases.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/tactic/util.h"
#include "library/tactic/proof_state.h"

namespace lean {
bool is_tactic_namespace_open(environment const & env) {
    for (name const & a : get_expr_aliases(env, "apply")) {
        if (a == get_tactic_apply_name()) {
            // make sure the type is the expected one
            if (auto d = env.find(a)) {
                expr t = d->get_type();
                if (is_pi(t)) {
                    expr b = binding_body(t);
                    if (!is_constant(b) || const_name(b) != get_tactic_name())
                        throw exception("tactic namespace declarations have been modified, "
                                        "function 'tactic.apply' is expected to return a 'tactic'");
                }
            }
            return true;
        }
    }
    return false;
}
}
