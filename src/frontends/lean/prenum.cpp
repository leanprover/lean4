/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/mpz.h"
#include "kernel/expr.h"

namespace lean {
expr mk_prenum(mpz const & v) {
    return mk_lit(literal(v));
}

bool is_prenum(expr const & e) {
    return is_lit(e) && lit_value(e).kind() == literal_kind::Nat;
}

mpz prenum_value(expr const & e) {
    lean_assert(is_prenum(e));
    return lit_value(e).get_nat().to_mpz();
}

void initialize_prenum() {
}

void finalize_prenum() {
}
}
