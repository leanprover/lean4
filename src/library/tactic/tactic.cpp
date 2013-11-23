/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <chrono>
#include "util/interrupt.h"
#include "util/lazy_list_fn.h"
#include "library/tactic/tactic_exception.h"
#include "library/tactic/tactic.h"

namespace lean {
tactic & tactic::operator=(tactic const & s) {
    LEAN_COPY_REF(tactic, s);
}

tactic & tactic::operator=(tactic && s) {
    LEAN_MOVE_REF(tactic, s);
}

expr tactic::solve(environment const & env, io_state const & io, proof_state const & s) {
    proof_state_seq r   = operator()(env, io, s);
    if (!r)
        throw exception("tactic failed to solve input");
    proof_state final = head(r);
    assignment a(final.get_menv());
    proof_map  m;
    return final.get_proof_builder()(m, env, a);
}

expr tactic::solve(environment const & env, io_state const & io, context const & ctx, expr const & t) {
    proof_state s = to_proof_state(env, ctx, t);
    return solve(env, io, s);
}

tactic id_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            return proof_state_seq(s);
        });
}

tactic fail_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const &) -> proof_state_seq {
            return proof_state_seq();
        });
}

tactic now_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            if (!empty(s.get_goals()))
                return proof_state_seq();
            else
                return proof_state_seq(s);
        });
}

tactic assumption_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            list<std::pair<name, expr>> proofs;
            goals new_goals = map_goals(s, [&](name const & ng, goal const & g) -> goal {
                    expr const & c  = g.get_conclusion();
                    expr pr;
                    for (auto const & p : g.get_hypotheses()) {
                        check_interrupted();
                        if (p.second == c) {
                            pr = mk_constant(p.first);
                            break;
                        }
                    }
                    if (pr) {
                        proofs.emplace_front(ng, pr);
                        return goal();
                    } else {
                        return g;
                    }
                });
            proof_builder p     = s.get_proof_builder();
            proof_builder new_p = mk_proof_builder([=](proof_map const & m, environment const & env, assignment const & a) -> expr {
                    proof_map new_m(m);
                    for (auto const & np : proofs) {
                        new_m.insert(np.first, np.second);
                    }
                    return p(new_m, env, a);
                });
            return proof_state_seq(proof_state(s, new_goals, new_p));
        });
}

tactic then(tactic t1, tactic t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            tactic _t1(t1);
            return map_append(_t1(env, io, s1), [=](proof_state const & s2) {
                    check_interrupted();
                    tactic _t2(t2);
                    return _t2(env, io, s2);
                });
        });
}

tactic orelse(tactic t1, tactic t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            tactic _t1(t1);
            proof_state_seq r = _t1(env, io, s);
            if (r) {
                return r;
            } else {
                check_interrupted();
                tactic _t2(t2);
                return _t2(env, io, s);
            }
        });
}

tactic try_for(tactic t, unsigned ms, unsigned check_ms) {
    if (check_ms == 0)
        check_ms = 1;
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            tactic _t(t);
            proof_state_seq         r;
            std::atomic<bool>       done(false);
            interruptible_thread th([&]() {
                    try {
                        r = _t(env, io, s);
                    } catch (...) {
                        r = proof_state_seq();
                    }
                    done = true;
                });
            try {
                auto start = std::chrono::steady_clock::now();
                std::chrono::milliseconds d(ms);
                std::chrono::milliseconds small(check_ms);
                while (!done) {
                    auto curr = std::chrono::steady_clock::now();
                    if (std::chrono::duration_cast<std::chrono::milliseconds>(curr - start) > d)
                        break;
                    check_interrupted();
                    std::this_thread::sleep_for(small);
                }
                th.request_interrupt();
                th.join();
                return r;
            } catch (...) {
                th.request_interrupt();
                th.join();
                throw;
            }
        });
}

tactic append(tactic t1, tactic t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            tactic _t1(t1);
            tactic _t2(t2);
            return append(_t1(env, io, s), _t2(env, io, s));
        });
}

tactic interleave(tactic t1, tactic t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            tactic _t1(t1);
            tactic _t2(t2);
            return interleave(_t1(env, io, s), _t2(env, io, s));
        });
}

tactic par(tactic t1, tactic t2, unsigned check_ms) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            tactic _t1(t1);
            tactic _t2(t2);
            proof_state_seq r1;
            proof_state_seq r2;
            std::atomic<bool>  done1(false);
            std::atomic<bool>  done2(false);
            interruptible_thread th1([&]() {
                    try {
                        r1 = _t1(env, io, s);
                    } catch (...) {
                        r1 = proof_state_seq();
                    }
                    done1 = true;
                });
            interruptible_thread th2([&]() {
                    try {
                        r2 = _t2(env, io, s);
                    } catch (...) {
                        r2 = proof_state_seq();
                    }
                    done2 = true;
                });
            try {
                std::chrono::milliseconds small(check_ms);
                while (!done1 && !done2) {
                    check_interrupted();
                    std::this_thread::sleep_for(small);
                }
                th1.request_interrupt();
                th2.request_interrupt();
                th1.join();
                th2.join();
                if (r1)
                    return r1;
                else
                    return r2;
            } catch (...) {
                th1.request_interrupt();
                th2.request_interrupt();
                th1.join();
                th2.join();
                throw;
            }
        });
}

tactic repeat(tactic t) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            tactic t1(t);
            proof_state_seq r = t1(env, io, s1);
            if (!r) {
                return proof_state_seq(s1);
            } else {
                return map_append(r, [=](proof_state const & s2) {
                        check_interrupted();
                        tactic t2 = repeat(t1);
                        return t2(env, io, s2);
                    });
            }
        });
}

tactic repeat_at_most(tactic t, unsigned k) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            if (k == 0)
                return proof_state_seq(s1);
            tactic t1(t);
            proof_state_seq r = t1(env, io, s1);
            if (!r) {
                return proof_state_seq(s1);
            } else {
                return map_append(r, [=](proof_state const & s2) {
                        check_interrupted();
                        tactic t2 = repeat_at_most(t1, k - 1);
                        return t2(env, io, s2);
                    });
            }
        });
}
}
