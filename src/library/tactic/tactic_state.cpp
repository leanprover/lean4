/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/trace.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_format.h"
#include "library/tactic/tactic_state.h"

namespace lean {
void tactic_state_cell::dealloc() {
    this->~tactic_state_cell();
    get_vm_allocator().deallocate(sizeof(tactic_state_cell), this);
}

tactic_state::tactic_state(environment const & env, options const & o, metavar_context const & ctx,
                           list<expr> const & gs, expr const & main) {
    m_ptr = new (get_vm_allocator().allocate(sizeof(tactic_state_cell))) tactic_state_cell(env, o, ctx, gs, main);
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, local_context const & lctx, expr const & type) {
    metavar_context mctx;
    expr main = mctx.mk_metavar_decl(lctx, type);
    return tactic_state(env, o, mctx, list<expr>(main), main);
}

tactic_state set_options(tactic_state const & s, options const & o) {
    return tactic_state(s.env(), o, s.mctx(), s.goals(), s.main());
}

tactic_state set_env(tactic_state const & s, environment const & env) {
    return tactic_state(env, s.get_options(), s.mctx(), s.goals(), s.main());
}

tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx) {
    return tactic_state(s.env(), s.get_options(), mctx, s.goals(), s.main());
}

tactic_state set_goals(tactic_state const & s, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), s.mctx(), gs, s.main());
}

tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), mctx, gs, s.main());
}

format tactic_state::pp_goal(formatter_factory const & fmtf, expr const & g) const {
    metavar_decl decl          = *mctx().get_metavar_decl(g);
    local_context const & lctx = decl.get_context();
    metavar_context mctx_tmp   = mctx();
    type_context ctx(env(), get_options(), mctx_tmp, lctx, transparency_mode::All);
    formatter fmt              = fmtf(env(), get_options(), ctx);
    format r                   = lctx.pp(fmt);
    unsigned indent            = get_pp_indent(get_options());
    bool unicode               = get_pp_unicode(get_options());
    if (!lctx.empty())
        r += line();
    format turnstile           = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    r += turnstile + space() + nest(indent, fmt(decl.get_type()));
    if (get_pp_goal_compact(get_options()))
        r = group(r);
    return r;
}

format tactic_state::pp(formatter_factory const & fmtf) const {
    format r;
    bool first = true;
    for (auto const & g : goals()) {
        if (first) first = false; else r += line() + line();
        r += pp_goal(fmtf, g);
    }
    if (first) r = format("no goals");
    return r;
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

vm_obj tactic_state_to_format(vm_obj const & s) {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return to_obj(to_tactic_state(s).pp(fmtf));
}

void initialize_tactic_state() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "env"}),       tactic_state_env);
    DECLARE_VM_BUILTIN(name({"tactic_state", "to_format"}), tactic_state_to_format);
}

void finalize_tactic_state() {
}
}
