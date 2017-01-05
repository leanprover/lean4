/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "library/io_state.h"
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
static tactic_state update_defeq_canonizer_state(tactic_state const & s, congruence_closure const & cc) {
    return set_env(s, cc.update_defeq_canonizer_state(s.env()));
}

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
    tactic_state const & s   = to_tactic_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    try {
        local_context lctx          = g->get_context();
        type_context ctx            = mk_type_context_for(s);
        congruence_closure::state r = mk_core(cfg);
        congruence_closure cc(ctx, r);
        lctx.for_each([&](local_decl const & d) {
                if (ctx.is_prop(d.get_type())) {
                    cc.add(d.get_type(), d.mk_ref());
                }
            });
        tactic_state new_s = update_defeq_canonizer_state(s, cc);
        return mk_tactic_success(to_obj(r), new_s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj cc_state_pp_core(vm_obj const & ccs, vm_obj const & nonsingleton, vm_obj const & _s) {
    tactic_state const & s   = to_tactic_state(_s);
    type_context ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqcs(fmt, to_bool(nonsingleton));
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
    tactic_state const & s   = to_tactic_state(_s);             \
    try {                                                       \
        type_context ctx            = mk_type_context_for(s);   \
        congruence_closure::state S = to_cc_state(ccs);         \
        congruence_closure cc(ctx, S);                          \
        CODE                                                    \
    } catch (exception & ex) {                                  \
        return mk_tactic_exception(ex, s);                      \
    }

#define cc_state_updt_proc(CODE) cc_state_proc({ CODE; return mk_tactic_success(to_obj(S), update_defeq_canonizer_state(s, cc)); })


vm_obj cc_state_add(vm_obj const & ccs, vm_obj const & H, vm_obj const & _s) {
    cc_state_updt_proc({
            expr type                   = ctx.infer(to_expr(H));
            if (ctx.is_prop(type))
                return mk_tactic_exception("cc_state.add failed, given expression is not a proof term", s);
            cc.add(type, to_expr(H));
    });
}

vm_obj cc_state_internalize(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_updt_proc({
            cc.internalize(to_expr(e));
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

vm_obj cc_state_false_proof(vm_obj const & ccs, vm_obj const & _s) {
    cc_state_proc({
            if (auto pr = cc.get_inconsistency_proof()) {
                return mk_tactic_success(to_obj(*pr), s);
            } else {
                return mk_tactic_exception("cc_state.false_proof failed, state is not inconsistent", s);
            }
        });
}

struct vm_ematch_state : public vm_external {
    ematch_state m_val;
    vm_ematch_state(ematch_state const & v): m_val(v) {}
    virtual ~vm_ematch_state() {}
    virtual void dealloc() override { this->~vm_ematch_state(); get_vm_allocator().deallocate(sizeof(vm_ematch_state), this); }
};

ematch_state const & to_ematch_state(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_ematch_state*>(to_external(o)));
    return static_cast<vm_ematch_state*>(to_external(o))->m_val;
}

vm_obj to_obj(ematch_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_ematch_state))) vm_ematch_state(s));
}

ematch_config to_ematch_config(vm_obj const & cfg) {
    ematch_config r;
    r.m_max_instances = force_to_unsigned(cfg);
    return r;
}

vm_obj ematch_state_mk(vm_obj const & cfg) {
    return to_obj(ematch_state(to_ematch_config(cfg)));
}

vm_obj ematch_state_internalize(vm_obj const & ems, vm_obj const & e, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    ematch_state S   = to_ematch_state(ems);
    type_context ctx = mk_type_context_for(s);
    S.internalize(ctx, to_expr(e));
    return mk_tactic_success(to_obj(S), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj mk_ematch_result(buffer<expr_pair> const & new_inst_buffer, congruence_closure::state const & ccs,
                        ematch_state const & ems) {
    vm_obj new_insts = mk_vm_nil();
    unsigned i = new_inst_buffer.size();
    while (i > 0) {
        --i;
        new_insts = mk_vm_cons(mk_vm_pair(to_obj(new_inst_buffer[i].first), to_obj(new_inst_buffer[i].second)), new_insts);
    }
    return mk_vm_pair(new_insts, mk_vm_pair(to_obj(ccs), to_obj(ems)));
}

vm_obj ematch_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & t, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx = mk_type_context_for(s, md);
    ematch_state ems = to_ematch_state(_ems);
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs);
    buffer<expr_pair> new_inst_buffer;
    ematch(ctx, ems, cc, to_hinst_lemma(hlemma), to_expr(t), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    tactic_state new_s = update_defeq_canonizer_state(to_tactic_state(s), cc);
    return mk_tactic_success(r, new_s);
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj ematch_all_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & filter, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx = mk_type_context_for(s, md);
    ematch_state ems = to_ematch_state(_ems);
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs);
    buffer<expr_pair> new_inst_buffer;
    ematch(ctx, ems, cc, to_hinst_lemma(hlemma), to_bool(filter), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    tactic_state new_s = update_defeq_canonizer_state(to_tactic_state(s), cc);
    return mk_tactic_success(r, new_s);
    LEAN_TACTIC_CATCH(to_tactic_state(s));
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
    DECLARE_VM_BUILTIN(name({"cc_state", "false_proof"}),          cc_state_false_proof);
    DECLARE_VM_BUILTIN(name({"cc_state", "eqv_proof"}),            cc_state_eqv_proof);

    DECLARE_VM_BUILTIN(name({"ematch_state", "mk"}),               ematch_state_mk);
    DECLARE_VM_BUILTIN(name({"ematch_state", "internalize"}),      ematch_state_internalize);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_core"}),            ematch_core);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_all_core"}),        ematch_all_core);
}

void finalize_congruence_tactics() {
}
}
