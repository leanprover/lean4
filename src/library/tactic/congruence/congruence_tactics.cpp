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
#include "library/tactic/tactic_state.h"
#include "library/tactic/congruence/congruence_closure.h"
#include "library/tactic/congruence/hinst_lemmas.h"
#include "library/tactic/congruence/ematch.h"

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

vm_obj cc_state_false_proof(vm_obj const & ccs, vm_obj const & _s) {
    cc_state_proc({
            if (auto pr = cc.get_inconsistency_proof()) {
                return mk_tactic_success(to_obj(*pr), s);
            } else {
                return mk_tactic_exception("cc_state.false_proof failed, state is not inconsistent", s);
            }
        });
}

struct vm_hinst_lemma : public vm_external {
    hinst_lemma m_val;
    vm_hinst_lemma(hinst_lemma const & v): m_val(v) {}
    virtual ~vm_hinst_lemma() {}
    virtual void dealloc() override { this->~vm_hinst_lemma(); get_vm_allocator().deallocate(sizeof(vm_hinst_lemma), this); }
};

hinst_lemma const & to_hinst_lemma(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_hinst_lemma*>(to_external(o)));
    return static_cast<vm_hinst_lemma*>(to_external(o))->m_val;
}

vm_obj to_obj(hinst_lemma const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_hinst_lemma))) vm_hinst_lemma(s));
}

vm_obj hinst_lemma_mk_core(vm_obj const & m, vm_obj const & lemma, vm_obj const & simp, vm_obj const & prio, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx        = mk_type_context_for(s, m);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_expr(lemma), to_bool(simp), force_to_unsigned(prio, 0));
    return mk_tactic_success(to_obj(h), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj hinst_lemma_mk_from_decl_core(vm_obj const & m, vm_obj const & lemma_name, vm_obj const & simp, vm_obj const & prio, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx        = mk_type_context_for(s, m);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_name(lemma_name), to_bool(simp), force_to_unsigned(prio, 0));
    return mk_tactic_success(to_obj(h), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj hinst_lemma_pp(vm_obj const & h, vm_obj const & _s) {
    tactic_state const & s = to_tactic_state(_s);
    LEAN_TACTIC_TRY;
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    type_context ctx = mk_type_context_for(s);
    formatter fmt = fmtf(s.env(), s.get_options(), ctx);
    format r = pp_hinst_lemma(fmt, to_hinst_lemma(h));
    return mk_tactic_success(to_obj(r), s);
    LEAN_TACTIC_CATCH(s);
}

struct vm_hinst_lemmas : public vm_external {
    hinst_lemmas m_val;
    vm_hinst_lemmas(hinst_lemmas const & v): m_val(v) {}
    virtual ~vm_hinst_lemmas() {}
    virtual void dealloc() override { this->~vm_hinst_lemmas(); get_vm_allocator().deallocate(sizeof(vm_hinst_lemmas), this); }
};

hinst_lemmas const & to_hinst_lemmas(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_hinst_lemmas*>(to_external(o)));
    return static_cast<vm_hinst_lemmas*>(to_external(o))->m_val;
}

vm_obj to_obj(hinst_lemmas const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_hinst_lemmas))) vm_hinst_lemmas(s));
}

vm_obj hinst_lemmas_mk() {
    return to_obj(hinst_lemmas());
}

vm_obj hinst_lemmas_add_core(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma, vm_obj const & simp, vm_obj const & prio, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx        = mk_type_context_for(s, m);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_expr(lemma), to_bool(simp), force_to_unsigned(prio, 0));
    hinst_lemmas new_lemmas = to_hinst_lemmas(lemmas);
    new_lemmas.insert(h);
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj hinst_lemmas_add_decl_core(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma_name, vm_obj const & simp, vm_obj const & prio, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx        = mk_type_context_for(s, m);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_name(lemma_name), to_bool(simp), force_to_unsigned(prio, 0));
    hinst_lemmas new_lemmas = to_hinst_lemmas(lemmas);
    new_lemmas.insert(h);
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
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

vm_obj ematch_state_mk(vm_obj const & max_instances) {
    return to_obj(ematch_state(force_to_unsigned(max_instances, std::numeric_limits<unsigned>::max())));
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
    return mk_tactic_success(r, to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj ematch_all_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & filter, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx = mk_type_context_for(s, md);
    ematch_state ems = to_ematch_state(_ems);
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs);
    buffer<expr_pair> new_inst_buffer;
    ematch_all(ctx, ems, cc, to_hinst_lemma(hlemma), to_bool(filter), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    return mk_tactic_success(r, to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

void initialize_congruence_tactics() {
    DECLARE_VM_BUILTIN(name({"cc_state", "mk"}),                   cc_state_mk);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_using_hs"}),          cc_state_mk_using_hs);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_core"}),              cc_state_pp_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_eqc"}),               cc_state_pp_eqc);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "root"}),                 cc_state_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "mt"}),                   cc_state_mt);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_cg_root"}),           cc_state_is_cg_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "roots_core"}),           cc_state_roots_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "internalize"}),          cc_state_internalize);
    DECLARE_VM_BUILTIN(name({"cc_state", "add"}),                  cc_state_add);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_eqv"}),               cc_state_is_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_not_eqv"}),           cc_state_is_not_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "inconsistent"}),         cc_state_inconsistent);
    DECLARE_VM_BUILTIN(name({"cc_state", "false_proof"}),          cc_state_false_proof);
    DECLARE_VM_BUILTIN(name({"cc_state", "eqv_proof"}),            cc_state_eqv_proof);

    DECLARE_VM_BUILTIN(name({"hinst_lemma", "mk_core"}),           hinst_lemma_mk_core);
    DECLARE_VM_BUILTIN(name({"hinst_lemma", "mk_from_decl_core"}), hinst_lemma_mk_from_decl_core);
    DECLARE_VM_BUILTIN(name({"hinst_lemma", "pp"}),                hinst_lemma_pp);

    DECLARE_VM_BUILTIN(name({"ematch_state", "mk"}),               ematch_state_mk);
    DECLARE_VM_BUILTIN(name({"ematch_state", "internalize"}),      ematch_state_internalize);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_core"}),            ematch_core);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_all_core"}),        ematch_all_core);
}

void finalize_congruence_tactics() {
}
}
