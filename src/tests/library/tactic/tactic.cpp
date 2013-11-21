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
    import_all(env);
    env.add_var("p", Bool);
    env.add_var("q", Bool);
    expr p = Const("p");
    expr q = Const("q");
    context ctx;
    ctx = extend(ctx, "H1", p);
    ctx = extend(ctx, "H2", q);
    // proof_state s1 = to_proof_state(env, ctx, mk_var(0));
    // tactic t = then(assumption_tactic(), now_tactic());
    // tactic_result_ref r = t(s1);
    // proof_state_ref s2 = r->next();
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
