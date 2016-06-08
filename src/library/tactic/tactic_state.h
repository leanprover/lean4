/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
#include "kernel/environment.h"
#include "library/metavar_context.h"

namespace lean {
class tactic_state_cell {
    MK_LEAN_RC();
    environment     m_env;
    options         m_options;
    metavar_context m_mctx;
    list<expr>      m_goals;
    friend class tactic_state;
    void dealloc();
public:
    tactic_state_cell(environment const & env, options const & o, metavar_context const & ctx, list<expr> const & gs):
        m_rc(1), m_env(env), m_options(o), m_mctx(ctx), m_goals(gs) {}
};

class tactic_state {
private:
    tactic_state_cell * m_ptr;
    tactic_state_cell * steal_ptr() { tactic_state_cell * r = m_ptr; m_ptr = nullptr; return r; }
    friend class optional<tactic_state>;
public:
    tactic_state(environment const & env, options const & o, metavar_context const & ctx, list<expr> const & gs);
    tactic_state(tactic_state const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic_state(tactic_state && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~tactic_state() { if (m_ptr) m_ptr->dec_ref(); }

    tactic_state_cell * raw() const { return m_ptr; }
    options const & get_options() const { lean_assert(m_ptr); return m_ptr->m_options; }
    environment const & env() const { lean_assert(m_ptr); return m_ptr->m_env; }
    metavar_context const & mctx() const { lean_assert(m_ptr); return m_ptr->m_mctx; }
    list<expr> const & goals() const { lean_assert(m_ptr); return m_ptr->m_goals; }

    tactic_state & operator=(tactic_state const & s) { LEAN_COPY_REF(s); }
    tactic_state & operator=(tactic_state && s) { LEAN_MOVE_REF(s); }

    friend void swap(tactic_state & a, tactic_state & b) { std::swap(a.m_ptr, b.m_ptr); }
    friend bool is_eqp(tactic_state const & a, tactic_state const & b) { return a.m_ptr == b.m_ptr; }
};

tactic_state set_options(tactic_state const & s, options const & o);
tactic_state set_env(tactic_state const & s, environment const & env);
tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx);
tactic_state set_goals(tactic_state const & s, list<expr> const & gs);
tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs);

tactic_state const & to_tactic_state(vm_obj const & o);
vm_obj to_obj(tactic_state const & s);

void initialize_tactic_state();
void finalize_tactic_state();
}
