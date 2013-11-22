/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/builtin.h"
#include "library/all/all.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
#include "library/tactic/tactic_exception.h"
using namespace lean;

static void tst1() {
    environment env;
    io_state io(options(), mk_simple_formatter());
    import_all(env);
    env.add_var("p", Bool);
    env.add_var("q", Bool);
    expr p = Const("p");
    expr q = Const("q");
    context ctx;
    ctx = extend(ctx, "H1", p);
    ctx = extend(ctx, "H2", q);
    proof_state s = to_proof_state(env, ctx, p);
    std::cout << s.pp(mk_simple_formatter(), options()) << "\n";
    tactic t = then(assumption_tactic(), now_tactic());
    std::cout << "proof 1: " << t.solve(env, io, s) << "\n";
    std::cout << "proof 2: " << t.solve(env, io, ctx, q) << "\n";
    try {
        now_tactic().solve(env, io, ctx, q);
        lean_unreachable();
    } catch (tactic_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
