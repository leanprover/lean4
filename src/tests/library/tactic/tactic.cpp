/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/test.h"
#include "util/interrupt.h"
#include "kernel/builtin.h"
#include "library/all/all.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
#include "library/tactic/tactic_exception.h"
using namespace lean;

tactic loop_tactic() {
    return mk_tactic([=](environment const &, io_state const &, proof_state const &) -> proof_state_seq {
            while (true) {
                check_interrupted();
            }
            return proof_state_seq();
        });
}

tactic msg_tactic(std::string msg) {
    return mk_tactic([=](environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            std::cout << msg << "\n";
            return proof_state_seq(s);
        });
}

tactic set_tactic(std::atomic<bool> * flag) {
    return mk_tactic([=](environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            *flag = true;
            return proof_state_seq(s);
        });
}

static void check_failure(tactic t, environment const & env, io_state const & io, context const & ctx, expr const & ty) {
    try {
        t.solve(env, io, ctx, ty);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

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
    check_failure(now_tactic(), env, io, ctx, q);
    std::cout << "proof 2: " << orelse(fail_tactic(), t).solve(env, io, ctx, q) << "\n";
#ifndef __APPLE__
    check_failure(try_for(loop_tactic(), 100), env, io, ctx, q);
    std::cout << "proof 1: " << try_for(t, 10000).solve(env, io, s) << "\n";
    check_failure(try_for(orelse(try_for(loop_tactic(), 10000),
                                 msg_tactic(std::string("hello world"))),
                          100),
                  env, io, ctx, q);
    std::atomic<bool> flag1(false);
    check_failure(try_for(orelse(try_for(loop_tactic(), 10000),
                                 set_tactic(&flag1)),
                          100),
                  env, io, ctx, q);
    lean_assert(!flag1);
    check_failure(orelse(try_for(try_for(loop_tactic(), 10000), 100),
                         set_tactic(&flag1)),
                  env, io, ctx, q);
    lean_assert(flag1);
#endif
    std::cout << "done\n";
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
