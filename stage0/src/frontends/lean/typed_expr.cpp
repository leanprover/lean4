/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/util.h"
#include "library/constants.h"

namespace lean {
bool is_typed_expr(expr const & e) {
    return is_app_of(e, get_typed_expr_name(), 2);
}

expr mk_typed_expr(expr const & t, expr const & v) {
    return mk_app(mk_constant(get_typed_expr_name()), t, v);
}

expr get_typed_expr_type(expr const & e) { lean_assert(is_typed_expr(e)); return app_arg(app_fn(e)); }
expr get_typed_expr_expr(expr const & e) { lean_assert(is_typed_expr(e)); return app_arg(e); }
}
