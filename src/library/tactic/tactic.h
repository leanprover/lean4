/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <memory>
#include <mutex>
#include "library/state.h"
#include "library/tactic/proof_state.h"

namespace lean {
typedef std::unique_ptr<proof_state> proof_state_ref;
class tactic_result;
typedef std::unique_ptr<tactic_result> tactic_result_ref;

class tactic_result {
    std::mutex        m_mutex;
    std::atomic<bool> m_interrupted;
protected:
    template<typename F>
    void exclusive_update(F && f) {
        std::lock_guard<std::mutex> lock(m_mutex);
        f();
    }
    virtual void interrupt();
    void propagate_interrupt(tactic_result_ref & r) { if (r) r->interrupt(); }
    virtual proof_state_ref next_core(environment const & env, state const & s) = 0;
public:
    tactic_result():m_interrupted(false) {}
    void request_interrupt();
    proof_state_ref next(environment const & env, state const & s);
    virtual ~tactic_result();
};

class tactic_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    virtual ~tactic_cell();
    virtual tactic_result_ref operator()(proof_state const & s) = 0;
};

class tactic {
protected:
    tactic_cell * m_ptr;
public:
    explicit tactic(tactic_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic(tactic const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic(tactic && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~tactic() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(tactic & a, tactic & b) { std::swap(a.m_ptr, b.m_ptr); }
    tactic & operator=(tactic const & s);
    tactic & operator=(tactic && s);

    tactic_result_ref operator()(proof_state const & s) { return m_ptr->operator()(s); }
};

template<typename F>
class simple_tactic_cell : public tactic_cell {
    F m_f;
public:
    simple_tactic_cell(F && f):m_f(f) {}

    class result : public tactic_result {
        simple_tactic_cell * m_cell;
        proof_state          m_in;
    public:
        result(simple_tactic_cell * c, proof_state const & in):m_cell(c), m_in(in) {
            lean_assert(m_cell);
            m_cell->inc_ref();
        }
        virtual ~result() { if (m_cell) m_cell->dec_ref(); }
        virtual proof_state_ref next_core(environment const & env, state const & io) {
            if (m_cell) {
                proof_state_ref r(new proof_state(m_cell->m_f(env, io, m_in)));
                m_cell = nullptr;
                return std::move(r);
            } else {
                return proof_state_ref();
            }
        }
    };

    virtual tactic_result_ref operator()(proof_state const & s) {
        return tactic_result_ref(new result(this, s));
    }
};


template<typename F>
tactic mk_tactic(F && f) { return tactic(new simple_tactic_cell<F>(std::forward<F>(f))); }

tactic id_tactic();
tactic fail_tactic();
tactic now_tactic();
tactic assumption_tactic();
tactic then(tactic const & t1, tactic const & t2);
}
