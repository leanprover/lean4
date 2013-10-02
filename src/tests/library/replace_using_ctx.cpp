/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/context.h"
#include "kernel/abstract.h"
#include "library/replace_using_ctx.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr N = Const("N");
    expr M = Const("M");
    expr x = Var(0);
    context ctx1;
    ctx1 = extend(ctx1, "x", N, a);
    context ctx2;
    ctx2 = extend(ctx2, "x", M, b);
    auto proc = [](expr const & e, context const & ctx, unsigned k) -> expr {
        if (is_var(e) && var_idx(e) < k) {
            context_entry const & entry = ctx.lookup(var_idx(e));
            if (entry.get_body())
                return entry.get_body();
        }
        return e;
    };
    replace_using_ctx_fn<decltype(proc)> replacer(proc);
    expr F1 = f(x);
    expr F1_copy = F1;
    lean_assert_eq(replacer(F1, ctx1), f(a));
    lean_assert_eq(replacer(F1, ctx2), f(b));
    lean_assert(is_eqp(replacer(F1, ctx2), replacer(F1, ctx2)));
    expr r1 = replacer(F1, ctx2);
    replacer.clear();
    lean_assert(!is_eqp(r1, replacer(F1, ctx2)));
    lean_assert(is_eqp(replacer(F1, ctx1), replacer(F1, ctx1)));
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
