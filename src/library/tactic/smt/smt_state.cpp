/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/app_builder.h"
#include "library/delayed_abstraction.h"
#include "library/type_context.h"
#include "library/vm/vm.h"
#include "library/vm/vm_format.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/change_tactic.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/smt_state.h"

namespace lean {
smt::goal::goal(smt_config const & cfg):
    m_cc_state(cfg.m_ho_fns, cfg.m_cc_config),
    m_em_state(cfg.m_em_config) {
}

smt::smt(type_context & ctx, goal & g):
    m_ctx(ctx),
    m_goal(g),
    m_cc(ctx, m_goal.m_cc_state) {
}

void smt::internalize(expr const & e, bool toplevel) {
    m_cc.internalize(e, toplevel);
    m_goal.m_em_state.internalize(m_ctx, e);
}

void smt::add(expr const & type, expr const & proof) {
    m_cc.add(type, proof);
}

struct vm_smt_state : public vm_external {
    smt_state m_val;
    vm_smt_state(smt_state const & v):m_val(v) {}
    virtual ~vm_smt_state() {}
    virtual void dealloc() override {
        this->~vm_smt_state(); get_vm_allocator().deallocate(sizeof(vm_smt_state), this);
    }
};

bool is_smt_state(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_smt_state*>(to_external(o));
}

smt_state const & to_smt_state(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_smt_state*>(to_external(o)));
    return static_cast<vm_smt_state*>(to_external(o))->m_val;
}

vm_obj to_obj(smt_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_smt_state))) vm_smt_state(s));
}

bool is_tactic_result_exception(vm_obj const & a) {
    return is_constructor(a) && cidx(a) == 1;
}

vm_obj mk_tactic_result(vm_obj const & a, vm_obj const & s) {
    lean_assert(is_tactic_state(s));
    return mk_vm_constructor(0, a, s);
}

vm_obj get_tactic_result_value(vm_obj const & r) {
    return cfield(r, 0);
}

vm_obj get_tactic_result_state(vm_obj const & r) {
    return cfield(r, 1);
}

vm_obj tactic_result_to_smt_tatic_result(vm_obj const & r, vm_obj const & s_state) {
    return mk_tactic_result(mk_vm_pair(get_tactic_result_value(r), s_state), get_tactic_result_state(r));
}

vm_obj mk_smt_tactic_success(vm_obj const & a, vm_obj const & s_state, vm_obj const & t_state) {
    return mk_vm_constructor(0, mk_vm_pair(a, s_state), t_state);
}

tactic_state revert_all(tactic_state const & s) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    local_context lctx       = g->get_context();
    buffer<expr> hs;
    lctx.for_each([&](local_decl const & d) { hs.push_back(d.mk_ref()); });
    return revert(hs, s);
}

vm_obj initial_dsimp(tactic_state const & s) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    type_context ctx         = mk_type_context_for(s, transparency_mode::Reducible);
    unsigned max_steps       = 10000000; /* TODO(Leo): move to smt_config */
    bool visit_instances     = false;
    expr target              = g->get_type();
    simp_lemmas_for no_lemmas;
    expr new_target          = dsimplify_fn(ctx, max_steps, visit_instances, no_lemmas)(target);
    return change(new_target, s);
}

vm_obj intro_all(tactic_state s, smt::goal new_goal) {
    lean_assert(s.goals());
    type_context ctx = mk_type_context_for(s, transparency_mode::Semireducible);
    smt S(ctx, new_goal);
    optional<metavar_decl> g = s.get_main_goal_decl();
    expr target = g->get_type();
    type_context::tmp_locals locals(ctx);
    buffer<expr> new_Hs;
    buffer<expr> to_inst;
    while (true) {
        if (!is_pi(target) && !is_let(target)) {
            target = instantiate_rev(target, to_inst.size(), to_inst.data());
            to_inst.clear();
            target = ctx.relaxed_try_to_pi(target);
        }
        if (is_pi(target)) {
            expr type = instantiate_rev(binding_domain(target), to_inst.size(), to_inst.data());
            name n    = ctx.get_unused_name(binding_name(target));
            expr h    = locals.push_local(n, type);
            to_inst.push_back(h);
            /* TODO(Leo): usual SMT preprocessing: destruct and/exists, push negation, ... */
            new_Hs.push_back(h);

            S.internalize(h, true);
            S.add(type, h);
            target = binding_body(target);
        } else if (is_let(target)) {
            expr type  = instantiate_rev(let_type(target), to_inst.size(), to_inst.data());
            expr value = instantiate_rev(let_value(target), to_inst.size(), to_inst.data());
            name n     = ctx.get_unused_name(let_name(target));
            expr h     = locals.push_let(n, type, value);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(type, true);
            S.internalize(value, true);
            /* TODO(Leo): add equality between h and value at CC? */
            S.add(type, h);
            target = let_body(target);
        } else {
            break;
        }
    }
    target = instantiate_rev(target, to_inst.size(), to_inst.data());

    expr new_M   = ctx.mk_metavar_decl(ctx.lctx(), target);
    expr new_val = abstract_locals(mk_delayed_abstraction_with_locals(new_M, new_Hs), new_Hs.size(), new_Hs.data());
    unsigned i   = new_Hs.size();
    while (i > 0) {
        --i;
        optional<local_decl> d = ctx.lctx().get_local_decl(new_Hs[i]);
        expr type = d->get_type();
        type      = abstract_locals(type, i, new_Hs.data());
        if (auto letval = d->get_value()) {
            letval    = abstract_locals(*letval, i, new_Hs.data());
            new_val   = mk_let(d->get_pp_name(), type, *letval, new_val);
        } else {
            new_val   = mk_lambda(d->get_pp_name(), type, new_val, d->get_info());
        }
    }
    lean_assert(!ctx.mctx().is_assigned(new_M));
    metavar_context mctx = ctx.mctx();
    mctx.assign(head(s.goals()), new_val);
    s = set_mctx_goals(s, mctx, cons(new_M, tail(s.goals())));
    return mk_tactic_success(to_obj(smt_state(new_goal)), s);
}

vm_obj mk_smt_state(tactic_state s, smt_config const & cfg) {
    if (!s.goals()) return mk_no_goals_exception(s);
    s = revert_all(s);
    vm_obj r = initial_dsimp(s);
    if (is_tactic_result_exception(r)) return r;
    s = to_tactic_state(get_tactic_result_state(r));
    smt::goal new_goal(cfg);
    return intro_all(s, new_goal);
}

/*
def default_smt_config : smt_config :=
{cc_cfg := default_cc_config,
 em_cfg := default_ematch_config}
*/
smt_config to_smt_config(vm_obj const & cfg) {
    smt_config r;
    std::tie(r.m_ho_fns, r.m_cc_config) = to_ho_fns_cc_config(cfield(cfg, 0));
    r.m_em_config                       = to_ematch_config(cfield(cfg, 1));
    return r;
}

vm_obj smt_state_mk(vm_obj const & cfg, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return mk_smt_state(to_tactic_state(s), to_smt_config(cfg));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

bool same_hyps(metavar_context const & mctx, expr const & mvar1, expr const & mvar2) {
    lean_assert(is_metavar(mvar1));
    lean_assert(is_metavar(mvar2));
    optional<metavar_decl> d1 = mctx.get_metavar_decl(mvar1);
    optional<metavar_decl> d2 = mctx.get_metavar_decl(mvar2);
    return d1 && d2 && equal_locals(d1->get_context(), d2->get_context());
}

vm_obj tactic_to_smt_tactic(vm_obj const &, vm_obj const & tac, vm_obj const & s_state, vm_obj const & t_state) {
    vm_obj r1 = invoke(tac, t_state);
    if (is_tactic_result_exception(r1)) {
        /* Tactic failed */
        return r1;
    }
    list<smt::goal> smt_goals = to_smt_state(s_state);
    if (!smt_goals) {
        /* There is no SMT state associated with any goal. */
        return tactic_result_to_smt_tatic_result(r1, s_state);
    }
    /* We only handle the common cases:
       1) goals is of the form (a_1, a_2, ..., a_m)
       2) new_goals is of the form (new_1, ... new_n, a_2, ..., a_m)
       3) the sets of hypotheses in new_1 ... new_n are equal to the
          set of hypotheses of a_1

       In this case, given a s_state of the form

          (s_1, ..., s_k)

       where k <= m, we obtain a new valid s_state

          (s_1, ..., s_1, s_2, ..., s_k)
           n copies of s_1
    */
    vm_obj new_t_state = get_tactic_result_state(r1);
    if (is_eqp(to_tactic_state(t_state), to_tactic_state(new_t_state))) {
        /* The tactic_state was not modified */
        return tactic_result_to_smt_tatic_result(r1, s_state);
    }
    list<expr> goals          = to_tactic_state(t_state).goals();
    list<expr> new_goals      = to_tactic_state(new_t_state).goals();
    if (goals == new_goals) {
        /* Set of goals did not change. */
        return tactic_result_to_smt_tatic_result(r1, s_state);
    }
    if (!new_goals) {
        /* There are no new goals */
        return tactic_result_to_smt_tatic_result(r1, to_obj(smt_state()));
    }
    if (!goals) {
        return mk_tactic_exception("failed to lift tactic to smt_tactic, there were no goals to be solved", to_tactic_state(t_state));
    }
    if (new_goals == tail(goals)) {
        /* Main goal was solved */
        if (smt_goals) {
            /* remove one SMT goal */
            smt_goals = tail(smt_goals);
        }
        return tactic_result_to_smt_tatic_result(r1, to_obj(smt_goals));
    }
    metavar_context const & mctx = to_tactic_state(new_t_state).mctx();
    if (tail(new_goals) == tail(goals) && same_hyps(mctx, head(new_goals), head(goals))) {
        /* The set of hypotheses in the main goal did not change */
        return tactic_result_to_smt_tatic_result(r1, s_state);
    }
    while (true) {
        if (!same_hyps(mctx, head(new_goals), head(goals))) {
            return mk_tactic_exception("failed to lift tactic to smt_tactic, set of hypotheses has been modified, this tactic has to be lifted manually",
                                       to_tactic_state(t_state));
        }
        if (tail(new_goals) == tail(goals)) {
            return tactic_result_to_smt_tatic_result(r1, to_obj(smt_goals));
        }
        /* copy smt state */
        smt_goals = cons(head(smt_goals), smt_goals);

        /* Move to next */
        new_goals = tail(new_goals);
        if (!new_goals) {
            return mk_tactic_exception("failed to lift tactic to smt_tactic, only tactics that modify a prefix of the list of goals can be automatically lifted",
                                       to_tactic_state(t_state));
        }
    }
}

vm_obj smt_state_to_format(vm_obj const & s_state, vm_obj const & t_state) {
    LEAN_TACTIC_TRY;
    tactic_state ts = to_tactic_state(t_state);
    format r;
    if (!ts.goals()) {
        r = format("no goals");
    } else {
        r = ts.pp_goal(head(ts.goals()));
        /* TODO(Leo): improve, we are just pretty printing equivalence classes. */
        /* TODO(Leo): disable local name purification */
        if (to_smt_state(s_state)) {
            congruence_closure::state ccs  = head(to_smt_state(s_state)).m_cc_state;
            type_context ctx               = mk_type_context_for(ts);
            formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
            formatter fmt                  = fmtf(ts.env(), ts.get_options(), ctx);
            format cc_fmt                  = ccs.pp_eqcs(fmt, true);
            r += line() + cc_fmt;
        }

        /* Pretty print type of remaining goals
           TODO(Leo): move this code to a different place */
        metavar_context mctx = ts.mctx();
        bool unicode         = get_pp_unicode(ts.get_options());
        format turnstile     = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
        for (expr const & g : tail(ts.goals())) {
            metavar_decl d = *mctx.get_metavar_decl(g);
            type_context ctx(ts.env(), ts.get_options(), mctx, d.get_context(), transparency_mode::Semireducible);
            formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
            formatter fmt                  = fmtf(ts.env(), ts.get_options(), ctx);
            r += line() + turnstile + space() + nest(3, fmt(d.get_type()));
        }
    }
    return to_obj(r);
    LEAN_TACTIC_CATCH(to_tactic_state(t_state));
}

void initialize_smt_state() {
    DECLARE_VM_BUILTIN(name({"smt_state", "mk"}),             smt_state_mk);
    DECLARE_VM_BUILTIN(name({"smt_state", "to_format"}),      smt_state_to_format);
    DECLARE_VM_BUILTIN("tactic_to_smt_tactic",                tactic_to_smt_tactic);
}

void finalize_smt_state() {
}
}
