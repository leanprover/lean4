/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <utility>
#include <memory>
#include <mutex>
#include "util/interrupt.h"
#include "util/lazy_list.h"
#include "library/io_state.h"
#include "library/tactic/proof_state.h"

namespace lean {
typedef lazy_list<proof_state> proof_state_seq;

class tactic_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    tactic_cell():m_rc(0) {}
    virtual ~tactic_cell() {}
    virtual proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) = 0;
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

    proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) { return m_ptr->operator()(env, io, s); }

    expr solve(environment const & env, io_state const & io, proof_state const & s);
    expr solve(environment const & env, io_state const & io, context const & ctx, expr const & t);
};

template<typename F>
class simple_tactic_cell : public tactic_cell {
    F m_f;
public:
    simple_tactic_cell(F && f):m_f(f) {}
    virtual proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) {
        return m_f(env, io, s);
    }
};

template<typename F>
tactic mk_tactic(F && f) { return tactic(new simple_tactic_cell<F>(std::forward<F>(f))); }

tactic id_tactic();
tactic fail_tactic();
tactic now_tactic();
tactic assumption_tactic();
tactic then(tactic t1, tactic t2);
tactic orelse(tactic t1, tactic t2);
tactic try_for(tactic t, unsigned ms, unsigned check_ms = g_small_sleep);
tactic repeat(tactic t1);
}
