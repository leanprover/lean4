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
#include "library/tactic/justification_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
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
    std::cout << "proof: " << t.solve(env, io, s) << "\n";
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
