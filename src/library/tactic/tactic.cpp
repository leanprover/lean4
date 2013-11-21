/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic.h"

namespace lean {
tactic_result::~tactic_result() {
}
void tactic_result::interrupt() {
    m_result = true;
}
void tactic_result::request_interrupt() {
    std::lock_guard<std::mutex> lock(m_mutex);
    interrupt();
}

tactic_cell::~tactic_cell() {
}

tactic & tactic::operator=(tactic const & s) {
    LEAN_COPY_REF(tactic, s);
}

tactic & tactic::operator=(tactic && s) {
    LEAN_MOVE_REF(tactic, s);
}

class id_tactic : public tactic_cell {
public:
    class result : public tactic_result {
        proof_state_ref m_r;
    public:
        result(proof_state const & s):m_r(new proof_state(s)) {}

        virtual proof_state_ref next() {
            return proof_state_ref(std::move(m_r));
        }
    };

    virtual tactic_result_ref operator()(proof_state const & s) const {
        return tactic_result_ref(new result(s));
    }
};

tactic idtac() { return tactic(new id_tactic()); }

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

        virtual proof_state_ref next() {
            if (m_r2) {
                proof_state_ref s2 = m_r2->next();
                if (s2)
                    return s2;
                m_r2.release();
                m_s1.release();
            }
            lean_assert(!m_r2);
            lean_assert(!m_s1);
            proof_state_ref new_s1(m_r1->next());
            if (!new_s1)
                return proof_state_ref(); // done, m_r1 has no more solutions
            m_s1.swap(new_s1);
            tactic_result_ref r2 = m_t2(proof_state(*m_s1));
            exclusive_update([&]() { m_r2.swap(r2); }); // must protect because interrupt() may be invoked from different thread
            return m_r2->next();
        }
    };

    virtual tactic_result_ref operator()(proof_state const & s) const {
        return tactic_result_ref(new result(m_t1(s), m_t2));
    }
};

tactic then(tactic const & t1, tactic const & t2) { return tactic(new then_tactic(t1, t2)); }
}
