/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <chrono>
#include <string>
#include "util/sstream.h"
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
    auto p = r.pull();
    if (!p)
        throw exception("tactic failed to solve input");
    proof_state final = p->first;
    assignment a(final.get_menv());
    proof_map  m;
    return final.get_proof_builder()(m, env, a);
}

expr tactic::solve(environment const & env, io_state const & io, context const & ctx, expr const & t) {
    proof_state s = to_proof_state(env, ctx, t);
    return solve(env, io, s);
}

tactic id_tactic() {
    return mk_simple_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state {
            return s;
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
                return to_proof_state_seq(s);
        });
}

tactic trace_tactic(std::string const & msg) {
    return mk_simple_tactic([=](environment const &, io_state const & io, proof_state const & s) -> proof_state {
            io.get_diagnostic_channel() << msg << "\n";
            io.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic trace_tactic(sstream const & msg) {
    return trace_tactic(msg.str());
}

tactic trace_tactic(char const * msg) {
    return trace_tactic(std::string(msg));
}

tactic assumption_tactic() {
    return mk_simple_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state {
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
            return proof_state(s, new_goals, new_p);
        });
}

tactic then(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return map_append(t1(env, io, s1), [=](proof_state const & s2) {
                    check_interrupted();
                    return t2(env, io, s2);
                });
        });
}

tactic orelse(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return orelse(t1(env, io, s), t2(env, io, s));
        });
}

tactic try_for(tactic const & t, unsigned ms, unsigned check_ms) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return timeout(t(env, io, s), ms, check_ms);
        });
}

tactic append(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return append(t1(env, io, s), t2(env, io, s));
        });
}

tactic interleave(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return interleave(t1(env, io, s), t2(env, io, s));
        });
}

tactic par(tactic const & t1, tactic const & t2, unsigned check_ms) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return par(t1(env, io, s), t2(env, io, s), check_ms);
        });
}

tactic repeat(tactic const & t) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return repeat(s1, [=](proof_state const & s2) {
                    return t(env, io, s2);
                });
        });
}

tactic repeat_at_most(tactic const & t, unsigned k) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return repeat_at_most(s1, [=](proof_state const & s2) {
                    return t(env, io, s2);
                }, k);
        });
}

tactic take(tactic const & t, unsigned k) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return take(k, t(env, io, s));
        });
}

tactic force(tactic const & t) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            proof_state_seq r = t(env, io, s);
            buffer<proof_state> buf;
            for_each(r, [&](proof_state const & s2) {
                    buf.push_back(s2);
                    check_interrupted();
                });
            return to_lazy(to_list(buf.begin(), buf.end()));
        });
}
}
