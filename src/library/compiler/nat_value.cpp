/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/mpz.h"
#include "kernel/expr.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/util.h"
#include "library/replace_visitor_with_tc.h"

namespace lean {
expr mk_nat_value(mpz const & v) {
    return mk_lit(literal(v));
}

bool is_nat_value(expr const & e) {
    return is_lit(e) && lit_value(e).kind() == literal_kind::Nat;
}

mpz get_nat_value_value(expr const & e) {
    lean_assert(is_nat_value(e));
    return lit_value(e).get_nat().to_mpz();
}

optional<expr> to_nat_value(type_context_old & ctx, expr const & e) {
    if (optional<mpz> v = to_num(e)) {
        expr type = ctx.whnf(ctx.infer(e));
        if (is_nat_type(type)) {
            return some_expr(mk_lit(literal(*v)));
        }
    }
    return none_expr();
}

class find_nat_values_fn : public replace_visitor_with_tc {
    expr visit_app(expr const & e) override {
        if (auto v = to_nat_value(m_ctx, e))
            return expr(*v);
        return replace_visitor_with_tc::visit_app(e);
    }
public:
    find_nat_values_fn(type_context_old & ctx):replace_visitor_with_tc(ctx) {}
};

expr find_nat_values(environment const & env, expr const & e) {
    type_context_old ctx(env, transparency_mode::All);
    return find_nat_values_fn(ctx)(e);
}

void initialize_nat_value() {
}

void finalize_nat_value() {
}
}
