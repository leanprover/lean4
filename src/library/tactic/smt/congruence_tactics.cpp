/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "library/io_state.h"
#include "library/util.h"
#include "library/app_builder.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/hinst_lemmas.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
struct vm_cc_state : public vm_external {
    congruence_closure::state m_val;
    vm_cc_state(congruence_closure::state const & v):m_val(v) {}
    virtual ~vm_cc_state() {}
    virtual void dealloc() override {
        this->~vm_cc_state(); get_vm_allocator().deallocate(sizeof(vm_cc_state), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_cc_state(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(m_val); }
};

bool is_cc_state(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_cc_state*>(to_external(o));
}

congruence_closure::state const & to_cc_state(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_cc_state*>(to_external(o)));
    return static_cast<vm_cc_state*>(to_external(o))->m_val;
}

vm_obj to_obj(congruence_closure::state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(s));
}

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
(em               : bool)
*/
pair<name_set, congruence_closure::config> to_ho_fns_cc_config(vm_obj const & cfg) {
    congruence_closure::config c;
    name_set ho_fns;
    c.m_ignore_instances = to_bool(cfield(cfg, 0));
    c.m_ac               = to_bool(cfield(cfg, 1));
    if (is_none(cfield(cfg, 2))) {
        c.m_all_ho       = true;
    } else {
        c.m_all_ho       = false;
        ho_fns           = to_name_set(to_list_name(get_some_value(cfield(cfg, 2))));
    }
    c.m_em               = to_bool(cfield(cfg, 3));
    return mk_pair(ho_fns, c);
}

static congruence_closure::state mk_core(vm_obj const & cfg) {
    congruence_closure::config c;
    name_set ho_fns;
    std::tie(ho_fns, c) = to_ho_fns_cc_config(cfg);
    return congruence_closure::state(ho_fns, c);
}

vm_obj cc_state_mk_core(vm_obj const & cfg) {
    return to_obj(mk_core(cfg));
}

vm_obj cc_state_mk_using_hs_core(vm_obj const & cfg, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    try {
        local_context lctx          = g->get_context();
        type_context_old ctx            = mk_type_context_for(s);
        defeq_can_state dcs         = s.dcs();
        congruence_closure::state r = mk_core(cfg);
        congruence_closure cc(ctx, r, dcs);
        lctx.for_each([&](local_decl const & d) {
                if (ctx.is_prop(d.get_type())) {
                    cc.add(d.get_type(), d.mk_ref(), 0);
                }
            });
        tactic_state new_s = set_dcs(s, dcs);
        return tactic::mk_success(to_obj(r), new_s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj cc_state_pp_core(vm_obj const & ccs, vm_obj const & nonsingleton, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    type_context_old ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqcs(fmt, to_bool(nonsingleton));
    return tactic::mk_success(to_obj(r), s);
}

vm_obj cc_state_pp_eqc(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    type_context_old ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqc(fmt, to_expr(e));
    return tactic::mk_success(to_obj(r), s);
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

vm_obj cc_state_roots_core(vm_obj const & ccs, vm_obj const & nonsingleton) {
    buffer<expr> roots;
    to_cc_state(ccs).get_roots(roots, to_bool(nonsingleton));
    return to_obj(roots);
}

vm_obj cc_state_inconsistent(vm_obj const & ccs) {
    return mk_vm_bool(to_cc_state(ccs).inconsistent());
}

vm_obj cc_state_mt(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_nat(to_cc_state(ccs).get_mt(to_expr(e)));
}

vm_obj cc_state_gmt(vm_obj const & ccs) {
    return mk_vm_nat(to_cc_state(ccs).get_gmt());
}

vm_obj cc_state_inc_gmt(vm_obj const & ccs) {
    congruence_closure::state s = to_cc_state(ccs);
    s.inc_gmt();
    return to_obj(s);
}

#define cc_state_proc(CODE)                                     \
    tactic_state const & s   = tactic::to_state(_s);             \
    try {                                                       \
        type_context_old ctx            = mk_type_context_for(s);   \
        congruence_closure::state S = to_cc_state(ccs);         \
        defeq_can_state dcs         = s.dcs();                  \
        congruence_closure cc(ctx, S, dcs);                     \
        CODE                                                    \
    } catch (exception & ex) {                                  \
        return tactic::mk_exception(ex, s);                      \
    }

#define cc_state_updt_proc(CODE) cc_state_proc({ CODE; return tactic::mk_success(to_obj(S), set_dcs(s, dcs)); })

vm_obj cc_state_add(vm_obj const & ccs, vm_obj const & H, vm_obj const & _s) {
    cc_state_updt_proc({
            expr type                   = ctx.infer(to_expr(H));
            if (!ctx.is_prop(type))
                return tactic::mk_exception("cc_state.add failed, given expression is not a proof term", s);
            cc.add(type, to_expr(H), 0);
    });
}

vm_obj cc_state_internalize(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_updt_proc({
            cc.internalize(to_expr(e), 0);
        });
}

vm_obj cc_state_is_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_eqv(to_expr(e1), to_expr(e2));
            return tactic::mk_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_is_not_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_not_eqv(to_expr(e1), to_expr(e2));
            return tactic::mk_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_eqv_proof(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_proof(to_expr(e1), to_expr(e2))) {
                return tactic::mk_success(to_obj(*r), s);
            } else {
                return tactic::mk_exception("cc_state.eqv_proof failed to build proof", s);
            }
        });
}

vm_obj cc_state_proof_for(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_eq_proof(to_expr(e), mk_true())) {
                return tactic::mk_success(to_obj(mk_of_eq_true(cc.ctx(), *r)), s);
            } else {
                return tactic::mk_exception("cc_state.get_proof_for failed to build proof", s);
            }
        });
}

vm_obj cc_state_refutation_for(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_eq_proof(to_expr(e), mk_false())) {
                return tactic::mk_success(to_obj(mk_not_of_eq_false(cc.ctx(), *r)), s);
            } else {
                return tactic::mk_exception("cc_state.get_refutation_for failed to build proof", s);
            }
        });
}

vm_obj cc_state_proof_for_false(vm_obj const & ccs, vm_obj const & _s) {
    cc_state_proc({
            if (auto pr = cc.get_inconsistency_proof()) {
                return tactic::mk_success(to_obj(*pr), s);
            } else {
                return tactic::mk_exception("cc_state.false_proof failed, state is not inconsistent", s);
            }
        });
}

void initialize_congruence_tactics() {
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_core"}),              cc_state_mk_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_using_hs_core"}),     cc_state_mk_using_hs_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_core"}),              cc_state_pp_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_eqc"}),               cc_state_pp_eqc);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "root"}),                 cc_state_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "mt"}),                   cc_state_mt);
    DECLARE_VM_BUILTIN(name({"cc_state", "gmt"}),                  cc_state_gmt);
    DECLARE_VM_BUILTIN(name({"cc_state", "inc_gmt"}),              cc_state_inc_gmt);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_cg_root"}),           cc_state_is_cg_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "roots_core"}),           cc_state_roots_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "internalize"}),          cc_state_internalize);
    DECLARE_VM_BUILTIN(name({"cc_state", "add"}),                  cc_state_add);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_eqv"}),               cc_state_is_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_not_eqv"}),           cc_state_is_not_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "inconsistent"}),         cc_state_inconsistent);
    DECLARE_VM_BUILTIN(name({"cc_state", "proof_for_false"}),      cc_state_proof_for_false);
    DECLARE_VM_BUILTIN(name({"cc_state", "eqv_proof"}),            cc_state_eqv_proof);
    DECLARE_VM_BUILTIN(name({"cc_state", "proof_for"}),            cc_state_proof_for);
    DECLARE_VM_BUILTIN(name({"cc_state", "refutation_for"}),       cc_state_refutation_for);
}

void finalize_congruence_tactics() {
}
}
