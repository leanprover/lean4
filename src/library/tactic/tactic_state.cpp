/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_environment.h"
#include "library/tactic/tactic_state.h"

namespace lean {
void tactic_state_cell::dealloc() {
    this->~tactic_state_cell();
    get_vm_allocator().deallocate(sizeof(tactic_state_cell), this);
}

tactic_state::tactic_state(environment const & env, options const & o, metavar_context const & ctx, list<expr> const & gs) {
    m_ptr = new (get_vm_allocator().allocate(sizeof(tactic_state_cell))) tactic_state_cell(env, o, ctx, gs);
}

tactic_state set_options(tactic_state const & s, options const & o) {
    return tactic_state(s.env(), o, s.mctx(), s.goals());
}

tactic_state set_env(tactic_state const & s, environment const & env) {
    return tactic_state(env, s.get_options(), s.mctx(), s.goals());
}

tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx) {
    return tactic_state(s.env(), s.get_options(), mctx, s.goals());
}

tactic_state set_goals(tactic_state const & s, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), s.mctx(), gs);
}

tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), mctx, gs);
}

struct vm_tactic_state : public vm_external {
    tactic_state m_val;
    vm_tactic_state(tactic_state const & v):m_val(v) {}
    virtual void dealloc() override {
        this->~vm_tactic_state(); get_vm_allocator().deallocate(sizeof(vm_tactic_state), this);
    }
};

tactic_state const & to_tactic_state(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_tactic_state*>(to_external(o)));
    return static_cast<vm_tactic_state*>(to_external(o))->m_val;
}

vm_obj to_obj(tactic_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_tactic_state))) vm_tactic_state(s));
}

vm_obj tactic_state_env(vm_obj const & s) {
    return to_obj(to_tactic_state(s).env());
}

void initialize_tactic_state() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "env"}),      tactic_state_env);
}

void finalize_tactic_state() {
}
}
