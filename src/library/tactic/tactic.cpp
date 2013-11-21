/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/interrupt.h"
#include "library/tactic/tactic_exception.h"
#include "library/tactic/tactic.h"

namespace lean {
tactic_result::~tactic_result() {
}
void tactic_result::interrupt() {
    m_interrupted = true;
}
void tactic_result::request_interrupt() {
    {
        std::lock_guard<std::mutex> lock(m_mutex);
        interrupt();
    }
    ::lean::request_interrupt();
}

proof_state_ref tactic_result::next(environment const & env, io_state const & s) {
    try {
        return next_core(env, s);
    } catch (interrupted &) {
        if (m_interrupted) {
            // promote to tactic_exception if tactic is marked as interrupted
            throw tactic_exception("interrupted");
        } else {
            // if tactic was not interrupted, then continue propagating interrupted exception
            throw;
        }
    }
}

tactic_cell::~tactic_cell() {
}

tactic & tactic::operator=(tactic const & s) {
    LEAN_COPY_REF(tactic, s);
}

tactic & tactic::operator=(tactic && s) {
    LEAN_MOVE_REF(tactic, s);
}

class then_tactic : public tactic_cell {
    tactic m_t1;
    tactic m_t2;
public:
    then_tactic(tactic const & t1, tactic const & t2):m_t1(t1), m_t2(t2) {}

    class result : public tactic_result {
        tactic_result_ref              m_r1;
        proof_state_ref                m_s1;
        tactic                         m_t2;
        tactic_result_ref              m_r2;
    protected:
        virtual void interrupt() {
            tactic_result::interrupt();
            propagate_interrupt(m_r1);
            propagate_interrupt(m_r2);
        }
    public:
        result(tactic_result_ref && r1, tactic const & t2):m_r1(std::move(r1)), m_t2(t2) {}

        virtual proof_state_ref next_core(environment const & env, io_state const & s) {
            if (m_r2) {
                proof_state_ref s2 = m_r2->next(env, s);
                if (s2)
                    return s2;
                m_r2.release();
                m_s1.release();
            }
            lean_assert(!m_r2);
            lean_assert(!m_s1);
            proof_state_ref new_s1(m_r1->next(env, s));
            if (!new_s1)
                return proof_state_ref(); // done, m_r1 has no more solutions
            m_s1.swap(new_s1);
            tactic_result_ref r2 = m_t2(proof_state(*m_s1));
            exclusive_update([&]() { m_r2.swap(r2); }); // must protect because interrupt() may be invoked from different thread
            return m_r2->next(env, s);
        }
    };

    virtual tactic_result_ref operator()(proof_state const & s) {
        return tactic_result_ref(new result(m_t1(s), m_t2));
    }
};

tactic then(tactic const & t1, tactic const & t2) { return tactic(new then_tactic(t1, t2)); }

tactic id_tactic() { return mk_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state { return s; }); }

tactic fail_tactic() { return mk_tactic([](environment const &, io_state const &, proof_state const &) -> proof_state { throw tactic_exception("failed"); }); }

tactic now_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state {
            if (!empty(s.get_goals()))
                throw tactic_exception("nowtac failed");
            return s;
        });
}

tactic assumption_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const & s) -> proof_state {
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
}
