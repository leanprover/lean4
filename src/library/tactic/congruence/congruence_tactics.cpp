/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/congruence/congruence_closure.h"

namespace lean {
struct vm_cc_state : public vm_external {
    congruence_closure::state m_val;
    vm_cc_state(congruence_closure::state const & v):m_val(v) {}
    virtual ~vm_cc_state() {}
    virtual void dealloc() override {
        this->~vm_cc_state(); get_vm_allocator().deallocate(sizeof(vm_cc_state), this);
    }
};

bool is_cc_state(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_cc_state*>(to_external(o));
}

congruence_closure::state const & to_cc_state(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_cc_state*>(to_external(o)));
    return static_cast<vm_cc_state*>(to_external(o))->m_val;
}

vm_obj to_obj(congruence_closure::state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(s));
}

vm_obj cc_state_mk() {
    return to_obj(congruence_closure::state());
}

vm_obj cc_state_mk_using_hs(vm_obj const & _s) {
    tactic_state const & s   = to_tactic_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    try {
        local_context lctx       = g->get_context();
        type_context ctx         = mk_type_context_for(s);
        congruence_closure::state r;
        congruence_closure cc(ctx, r);
        lctx.for_each([&](local_decl const & d) {
                if (ctx.is_prop(d.get_type())) {
                    cc.add(d.get_type(), d.mk_ref());
                }
            });
        return mk_tactic_success(to_obj(r), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj cc_state_pp(vm_obj const & ccs, vm_obj const & _s) {
    tactic_state const & s   = to_tactic_state(_s);
    type_context ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqcs(fmt);
    return mk_tactic_success(to_obj(r), s);
}

void initialize_congruence_tactics() {
    DECLARE_VM_BUILTIN(name({"cc_state", "mk"}),               cc_state_mk);
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_using_hs"}),      cc_state_mk_using_hs);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp"}),               cc_state_pp);
}

void finalize_congruence_tactics() {
}
}
