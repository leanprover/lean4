/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/simplifier/simp_tactic.h"

namespace lean {
expr mk_simp_tactic_expr(buffer<expr> const & /* ls */, buffer<name> const & /* ns */,
                         buffer<name> const & /* ex */, optional<expr> const & /* pre_tac */,
                         location const & /* loc */) {
    // TODO(Leo)
    return mk_constant(get_tactic_fail_name());
}
}
