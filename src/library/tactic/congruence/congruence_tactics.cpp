/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/io_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
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

vm_obj cc_state_pp_eqc(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s   = to_tactic_state(_s);
    type_context ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqc(fmt, to_expr(e));
    return mk_tactic_success(to_obj(r), s);
}

vm_obj cc_state_next(vm_obj const & ccs, vm_obj const & e) {
    return to_obj(to_cc_state(ccs).get_next(to_expr(e)));
}

vm_obj cc_state_root(vm_obj const & ccs, vm_obj const & e) {
    return to_obj(to_cc_state(ccs).get_root(to_expr(e)));
}

vm_obj cc_state_is_cg_root(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_bool(to_cc_state(ccs).is_congr_root(to_expr(e)));
}

vm_obj cc_state_roots(vm_obj const & ccs) {
    buffer<expr> roots;
    to_cc_state(ccs).get_roots(roots);
    return to_obj(roots);
}

vm_obj cc_state_inconsistent(vm_obj const & ccs) {
    return mk_vm_bool(to_cc_state(ccs).inconsistent());
}

vm_obj cc_state_mt(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_nat(to_cc_state(ccs).get_mt(to_expr(e)));
}

#define cc_state_proc(CODE)                                     \
    tactic_state const & s   = to_tactic_state(_s);             \
    try {                                                       \
        type_context ctx            = mk_type_context_for(s);   \
        congruence_closure::state S = to_cc_state(ccs);         \
        congruence_closure cc(ctx, S);                          \
        CODE                                                    \
    } catch (exception & ex) {                                  \
        return mk_tactic_exception(ex, s);                      \
    }

#define cc_state_updt_proc(CODE) cc_state_proc({ CODE; return mk_tactic_success(to_obj(S), s); })


vm_obj cc_state_add(vm_obj const & ccs, vm_obj const & H, vm_obj const & _s) {
    cc_state_updt_proc({
            expr type                   = ctx.infer(to_expr(H));
            if (ctx.is_prop(type))
                return mk_tactic_exception("cc_state.add failed, given expression is not a proof term", s);
            cc.add(type, to_expr(H));
        });
}

vm_obj cc_state_internalize(vm_obj const & ccs, vm_obj const & e, vm_obj const & top_level, vm_obj const & _s) {
    cc_state_updt_proc({
            cc.internalize(to_expr(e), to_bool(top_level));
        });
}

vm_obj cc_state_is_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_eqv(to_expr(e1), to_expr(e2));
            return mk_tactic_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_is_not_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_not_eqv(to_expr(e1), to_expr(e2));
            return mk_tactic_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_eqv_proof(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_proof(to_expr(e1), to_expr(e2))) {
                return mk_tactic_success(to_obj(*r), s);
            } else {
                return mk_tactic_exception("cc_state.eqv_proof failed to build proof", s);
            }
        });
}

void initialize_congruence_tactics() {
    DECLARE_VM_BUILTIN(name({"cc_state", "mk"}),               cc_state_mk);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),             cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_using_hs"}),      cc_state_mk_using_hs);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp"}),               cc_state_pp);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_eqc"}),           cc_state_pp_eqc);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),             cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "root"}),             cc_state_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "mt"}),               cc_state_mt);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_cg_root"}),       cc_state_is_cg_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "roots"}),            cc_state_roots);
    DECLARE_VM_BUILTIN(name({"cc_state", "internalize"}),      cc_state_internalize);
    DECLARE_VM_BUILTIN(name({"cc_state", "add"}),              cc_state_add);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_eqv"}),           cc_state_is_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_not_eqv"}),       cc_state_is_not_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "eqv_proof"}),        cc_state_eqv_proof);
}

void finalize_congruence_tactics() {
}
}
