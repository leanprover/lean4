/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Rob Lewis
*/
#include "library/norm_num.h"
namespace lean {
bool norm_num_context::is_numeral(expr const &) const {
    // TODO(Rob)
    return false;
}

pair<expr, expr> norm_num_context::mk_norm(expr const &) {
    // TODO(Rob)
    throw exception("not implemented yet - norm_num`");
}
}
