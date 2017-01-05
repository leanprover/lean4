/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/pp_options.h"
#include "library/delayed_abstraction.h"
#include "library/type_context.h"
#include "library/trace.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/tactic/user_attribute.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/simplify.h"
#include "library/tactic/change_tactic.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/smt_state.h"

namespace lean {
smt_goal::smt_goal(smt_config const & cfg):
    m_cc_state(cfg.m_ho_fns, cfg.m_cc_config),
    m_em_state(cfg.m_em_config, cfg.m_em_lemmas),
    m_pre_config(cfg.m_pre_config) {
}

smt::smt(type_context & ctx, smt_goal & g):
    m_ctx(ctx),
    m_goal(g),
    m_cc(ctx, m_goal.m_cc_state, this) {
}

smt::~smt() {
}

void smt::propagated(unsigned n, expr const * p) {
    lean_trace(name({"smt", "units"}), scope_trace_env _(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               format r;
               for (unsigned i = 0; i < n; i++) { if (i > 0) r += comma() + line(); r += fmt(p[i]); }
               tout() << group(format("new facts:") + line() + bracket("{", r, "}")) << "\n";);
}

lbool smt::get_value_core(expr const & e) {
    if (m_cc.is_eqv(e, mk_true())) return l_true;
    if (m_cc.is_eqv(e, mk_false())) return l_false;
    return l_undef;
}

lbool smt::get_value(expr const & e) {
    lbool r = get_value_core(e);
    if (r != l_undef) return r;
    expr arg;
    if (is_not(e, arg)) {
        return ~get_value_core(arg);
    }
    return l_undef;
}

optional<expr> smt::get_proof(expr const & e) {
    if (m_cc.is_eqv(e, mk_true()))
        if (auto pr = m_cc.get_eq_proof(e, mk_true()))
            return some_expr(mk_of_eq_true(m_ctx, *pr));
    expr arg;
    if (is_not(e, arg) && m_cc.is_eqv(arg, mk_false()))
        if (auto pr = m_cc.get_eq_proof(arg, mk_false()))
            return some_expr(mk_not_of_eq_false(m_ctx, *pr));
    return none_expr();
}

void smt::internalize(expr const & e) {
    m_cc.internalize(e);
    m_goal.m_em_state.internalize(m_ctx, e);
}

void smt::add(expr const & type, expr const & proof) {
    m_goal.m_em_state.internalize(m_ctx, type);
    m_cc.add(type, proof);
}

void smt::ematch(buffer<expr_pair> & result) {
    ::lean::ematch(m_ctx, m_goal.m_em_state, m_cc, result);
}

struct vm_smt_goal : public vm_external {
    smt_goal m_val;
    vm_smt_goal(smt_goal const & v):m_val(v) {}
    virtual ~vm_smt_goal() {}
    virtual void dealloc() override {
        this->~vm_smt_goal(); get_vm_allocator().deallocate(sizeof(vm_smt_goal), this);
    }
};

bool is_smt_goal(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_smt_goal*>(to_external(o));
}

smt_goal const & to_smt_goal(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_smt_goal*>(to_external(o)));
    return static_cast<vm_smt_goal*>(to_external(o))->m_val;
}

vm_obj to_obj(smt_goal const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_smt_goal))) vm_smt_goal(s));
}

vm_obj tactic_result_to_smt_tactic_result(vm_obj const & r, vm_obj const & ss) {
    return mk_tactic_result(mk_vm_pair(get_tactic_result_value(r), ss), get_tactic_result_state(r));
}

vm_obj mk_smt_tactic_success(vm_obj const & a, vm_obj const & ss, vm_obj const & ts) {
    return mk_vm_constructor(0, mk_vm_pair(a, ss), ts);
}

vm_obj mk_smt_tactic_success(vm_obj const & ss, vm_obj const & ts) {
    return mk_smt_tactic_success(mk_vm_unit(), ss, ts);
}

vm_obj mk_smt_tactic_success(vm_obj const & ss, tactic_state const & ts) {
    return mk_smt_tactic_success(ss, to_obj(ts));
}

tactic_state revert_all(tactic_state const & s) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    local_context lctx       = g->get_context();
    buffer<expr> hs;
    lctx.for_each([&](local_decl const & d) { hs.push_back(d.mk_ref()); });
    return revert(hs, s);
}

static dsimplify_fn mk_dsimp(type_context & ctx, smt_pre_config const & cfg) {
    unsigned max_steps       = cfg.m_max_steps;
    bool visit_instances     = false;
    simp_lemmas_for eq_lemmas;
    if (auto r = cfg.m_simp_lemmas.find(get_eq_name()))
        eq_lemmas = *r;
    return dsimplify_fn(ctx, max_steps, visit_instances, eq_lemmas);
}

static simplify_fn mk_simp(type_context & ctx, smt_pre_config const & cfg) {
    unsigned max_steps       = cfg.m_max_steps;
    bool contextual          = false;
    bool lift_eq             = true;
    bool canonize_instances  = true;
    bool canonize_proofs     = false;
    bool use_axioms          = true;
    return simplify_fn(ctx, cfg.m_simp_lemmas, max_steps,
                       contextual, lift_eq, canonize_instances,
                       canonize_proofs, use_axioms);
}

static simp_result preprocess(type_context & ctx, smt_pre_config const & cfg, expr const & e) {
    type_context::zeta_scope _1(ctx, cfg.m_zeta);
    dsimplify_fn dsimp       = mk_dsimp(ctx, cfg);
    expr new_e               = dsimp(e);
    ctx.set_env(dsimp.update_defeq_canonizer_state(ctx.env()));
    simplify_fn simp         = mk_simp(ctx, cfg);
    simp_result r            = simp(get_eq_name(), new_e);
    ctx.set_env(simp.update_defeq_canonizer_state(ctx.env()));
    return r;
}

static vm_obj preprocess(tactic_state s, smt_pre_config const & cfg) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    type_context ctx         = mk_type_context_for(s, transparency_mode::Reducible);
    expr target              = g->get_type();
    simp_result r            = preprocess(ctx, cfg, target);
    if (!r.has_proof()) {
        s = set_env(s, ctx.env());
        return change(r.get_new(), s);
    } else {
        expr new_M           = ctx.mk_metavar_decl(ctx.lctx(), r.get_new());
        expr h               = mk_app(ctx, get_eq_mpr_name(), r.get_proof(), new_M);
        metavar_context mctx = ctx.mctx();
        mctx.assign(head(s.goals()), h);
        tactic_state new_s   = set_env_mctx_goals(s, ctx.env(), mctx, cons(new_M, tail(s.goals())));
        return mk_tactic_success(new_s);
    }
}

expr intros(environment const & env, options const & opts, metavar_context & mctx, expr const & mvar, smt_goal & s_goal,
            bool use_unused_names) {
    optional<metavar_decl> decl = mctx.get_metavar_decl(mvar);
    lean_assert(decl);
    type_context ctx(env, opts, mctx, decl->get_context(), transparency_mode::Semireducible);
    smt S(ctx, s_goal);
    expr target = decl->get_type();
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
            name n    = binding_name(target);
            if (use_unused_names) n = ctx.get_unused_name(n);
            expr h    = locals.push_local(n, type);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(h);
            S.add(type, h);
            target = binding_body(target);
        } else if (is_let(target)) {
            expr type  = instantiate_rev(let_type(target), to_inst.size(), to_inst.data());
            expr value = instantiate_rev(let_value(target), to_inst.size(), to_inst.data());
            name n     = let_name(target);
            if (use_unused_names) n = ctx.get_unused_name(n);
            expr h     = locals.push_let(n, type, value);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(type);
            S.internalize(value);
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
    mctx = ctx.mctx();
    mctx.assign(mvar, new_val);
    return new_M;
}

vm_obj mk_smt_state(tactic_state s, smt_config const & cfg) {
    if (!s.goals()) return mk_no_goals_exception(s);
    s = revert_all(s);

    smt_goal new_goal(cfg);

    vm_obj r = preprocess(s, cfg.m_pre_config);
    if (is_tactic_result_exception(r)) return r;
    s = to_tactic_state(get_tactic_result_state(r));

    metavar_context mctx = s.mctx();
    bool use_unused_names = true;
    expr new_M = intros(s.env(), s.get_options(), mctx, head(s.goals()), new_goal, use_unused_names);
    s = set_mctx_goals(s, mctx, cons(new_M, tail(s.goals())));
    return mk_tactic_success(mk_vm_cons(to_obj(new_goal), mk_vm_nil()), s);
}

static hinst_lemmas get_hinst_lemmas(name const & attr_name, tactic_state const & s) {
    auto & S      = get_vm_state();
    vm_obj attr   = S.get_constant(attr_name);
    vm_obj r      = caching_user_attribute_get_cache(mk_vm_unit(), attr, to_obj(s));
    if (is_tactic_result_exception(r))
        throw exception(sstream() << "failed to initialize sm_state, failed to retrieve attribute '" << attr_name << "'");
    vm_obj lemmas = get_tactic_result_value(r);
    if (!is_hinst_lemmas(lemmas))
        throw exception(sstream() << "failed to initialize smt_state, attribute '" << attr_name << "' is not a hinst_lemmas");
    return to_hinst_lemmas(lemmas);
}

static simp_lemmas get_simp_lemmas(name const & attr_name, tactic_state const & s) {
    auto & S      = get_vm_state();
    vm_obj attr   = S.get_constant(attr_name);
    vm_obj r      = caching_user_attribute_get_cache(mk_vm_unit(), attr, to_obj(s));
    if (is_tactic_result_exception(r))
        throw exception(sstream() << "failed to initialize sm_state, failed to retrieve attribute '" << attr_name << "'");
    vm_obj lemmas = get_tactic_result_value(r);
    if (!is_simp_lemmas(lemmas))
        throw exception(sstream() << "failed to initialize smt_state, attribute '" << attr_name << "' is not a simp_lemmas");
    return to_simp_lemmas(lemmas);
}

/*
structure smt_pre_config :=
(simp_attr : name)
(max_steps : nat)
(zeta      : bool)
*/
static smt_pre_config to_smt_pre_config(vm_obj const & cfg, tactic_state const & s) {
    smt_pre_config r;
    r.m_simp_lemmas   = get_simp_lemmas(to_name(cfield(cfg, 0)), s);
    r.m_max_steps     = force_to_unsigned(cfield(cfg, 1));
    r.m_zeta          = to_bool(cfield(cfg, 2));
    return r;
}

/*
structure smt_config :=
(cc_cfg        : cc_config)
(em_cfg        : ematch_config)
(pre_cfg       : smt_pre_config)
(em_attr       : name)
*/
static smt_config to_smt_config(vm_obj const & cfg, tactic_state const & s) {
    smt_config r;
    std::tie(r.m_ho_fns, r.m_cc_config) = to_ho_fns_cc_config(cfield(cfg, 0));
    r.m_em_config                       = to_ematch_config(cfield(cfg, 1));
    r.m_pre_config                      = to_smt_pre_config(cfield(cfg, 2), s);
    r.m_em_lemmas                       = get_hinst_lemmas(to_name(cfield(cfg, 3)), s);
    return r;
}

vm_obj smt_state_mk(vm_obj const & cfg, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return mk_smt_state(to_tactic_state(s), to_smt_config(cfg, to_tactic_state(s)));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

bool same_hyps(metavar_context const & mctx, expr const & mvar1, expr const & mvar2) {
    lean_assert(is_metavar(mvar1));
    lean_assert(is_metavar(mvar2));
    optional<metavar_decl> d1 = mctx.get_metavar_decl(mvar1);
    optional<metavar_decl> d2 = mctx.get_metavar_decl(mvar2);
    return d1 && d2 && equal_locals(d1->get_context(), d2->get_context());
}

vm_obj tactic_to_smt_tactic(vm_obj const &, vm_obj const & tac, vm_obj const & ss, vm_obj const & ts) {
    vm_obj r1 = invoke(tac, ts);
    if (is_tactic_result_exception(r1)) {
        /* Tactic failed */
        return r1;
    }
    if (is_nil(ss)) {
        /* There is no SMT state associated with any goal. */
        return tactic_result_to_smt_tactic_result(r1, ss);
    }
    /* We only handle the common cases:
       1) goals is of the form (a_1, a_2, ..., a_m)
       2) new_goals is of the form (new_1, ... new_n, a_2, ..., a_m)
       3) the sets of hypotheses in new_1 ... new_n are equal to the
          set of hypotheses of a_1

       In this case, given a ss of the form

          (s_1, ..., s_k)

       where k <= m, we obtain a new valid ss

          (s_1, ..., s_1, s_2, ..., s_k)
           n copies of s_1
    */
    vm_obj new_ts = get_tactic_result_state(r1);
    if (is_eqp(to_tactic_state(ts), to_tactic_state(new_ts))) {
        /* The tactic_state was not modified */
        return tactic_result_to_smt_tactic_result(r1, ss);
    }
    list<expr> goals          = to_tactic_state(ts).goals();
    list<expr> new_goals      = to_tactic_state(new_ts).goals();
    if (goals == new_goals) {
        /* Set of goals did not change. */
        return tactic_result_to_smt_tactic_result(r1, ss);
    }
    if (!new_goals) {
        /* There are no new goals */
        return tactic_result_to_smt_tactic_result(r1, mk_vm_nil());
    }
    if (!goals) {
        return mk_tactic_exception("failed to lift tactic to smt_tactic, there were no goals to be solved", to_tactic_state(ts));
    }
    if (new_goals == tail(goals)) {
        /* Main goal was solved */
        /* remove one SMT goal */
        vm_obj new_ss = tail(ss);
        return tactic_result_to_smt_tactic_result(r1, new_ss);
    }
    metavar_context const & mctx = to_tactic_state(new_ts).mctx();
    if (tail(new_goals) == tail(goals) && same_hyps(mctx, head(new_goals), head(goals))) {
        /* The set of hypotheses in the main goal did not change */
        return tactic_result_to_smt_tactic_result(r1, ss);
    }
    vm_obj new_ss = ss;
    while (true) {
        if (!same_hyps(mctx, head(new_goals), head(goals))) {
            return mk_tactic_exception("failed to lift tactic to smt_tactic, set of hypotheses has been modified, at least one of the used tactics has to be lifted manually",
                                       to_tactic_state(ts));
        }
        if (tail(new_goals) == tail(goals)) {
            return tactic_result_to_smt_tactic_result(r1, new_ss);
        }
        /* copy smt state */
        new_ss = mk_vm_cons(head(new_ss), new_ss);

        /* Move to next */
        new_goals = tail(new_goals);
        if (!new_goals) {
            return mk_tactic_exception("failed to lift tactic to smt_tactic, only tactics that modify a prefix of the list of goals can be automatically lifted",
                                       to_tactic_state(ts));
        }
    }
}

static bool ignore_pp_fact(expr const & e) {
    return
        is_arrow(e) ||
        is_true(e) ||
        is_false(e) ||
        is_or(e) ||
        is_and(e) ||
        is_not(e) ||
        is_iff(e) ||
        is_ite(e);
}

static optional<format> pp_facts(cc_state const & ccs, expr const & root, formatter const & fmt) {
    optional<format> r;
    expr it = root;
    do {
        if (!ignore_pp_fact(it)) {
            if (r)
                r = *r + comma() + line() + fmt(it);
            else
                r = fmt(it);
        }
        it = ccs.get_next(it);
    } while (it != root);
    return r;
}

static format pp_positive_facts(cc_state const & ccs, formatter const & fmt) {
    if (auto r = pp_facts(ccs, mk_true(), fmt))
        return group(format("facts:") + line() + bracket("{", *r, "}")) + line();
    else
        return format();
}

static format pp_negative_facts(cc_state const & ccs, formatter const & fmt) {
    if (auto r = pp_facts(ccs, mk_false(), fmt))
        return group(format("refuted facts:") + line() + bracket("{", *r, "}")) + line();
    else
        return format();
}

static format pp_equivalences(type_context & ctx, cc_state const & ccs, formatter const & fmt) {
    format r;
    bool first = true;
    buffer<expr> roots;
    ccs.get_roots(roots);
    for (expr const & root : roots) {
        if (root == mk_true() || root == mk_false()) continue;
        if (ctx.is_proof(root)) continue;
        if (first) first = false; else r += comma() + line();
        r += ccs.pp_eqc(fmt, root);
    }
    if (!first) {
        return group(format("equalities:") + line() + bracket("{", r, "}")) + line();
    } else {
        return format();
    }
}

format smt_goal_to_format(smt_goal sg, tactic_state const & ts) {
    lean_assert(ts.goals());
    options opts               = ts.get_options().update_if_undef(get_pp_purify_locals_name(), false);
    bool inst_mvars            = get_pp_instantiate_goal_mvars(opts);
    bool unicode               = get_pp_unicode(opts);
    unsigned indent            = get_pp_indent(opts);
    metavar_decl decl          = *ts.get_main_goal_decl();
    local_context lctx         = decl.get_context();
    metavar_context mctx_tmp   = ts.mctx();
    expr target                = decl.get_type();
    if (inst_mvars)
        target                 = mctx_tmp.instantiate_mvars(target);
    format turnstile           = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    type_context ctx(ts.env(), opts, mctx_tmp, lctx, transparency_mode::All);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt              = fmtf(ts.env(), opts, ctx);
    smt S(ctx, sg);
    format r;
    if (S.inconsistent()) {
        r  = format("contradictory goal, use 'smt_tactic.close' to close this goal");
        r += line();
    } else {
        if (inst_mvars)
            lctx                   = lctx.instantiate_mvars(mctx_tmp);
        /* TODO(Leo): add support for hidding hypotheses */
        r                          = lctx.pp(fmt, [&](local_decl const &) { return true; });
        if (!lctx.empty())
            r += line();
        cc_state ccs               = sg.get_cc_state();
        r += pp_positive_facts(ccs, fmt);
        r += pp_negative_facts(ccs, fmt);
        r += pp_equivalences(ctx, ccs, fmt);
    }
    r += turnstile + space() + nest(indent, fmt(target));
    return r;
}

format smt_state_to_format_core(vm_obj const & ss, tactic_state const & ts) {
    if (!ts.goals()) return format("no goals");
    if (is_nil(ss))  return ts.pp(); /* fallback */
    format r;
    r = smt_goal_to_format(to_smt_goal(head(ss)), ts);

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
        r += line() + line() + turnstile + space() + nest(3, fmt(d.get_type()));
    }
    return r;
}

format smt_state_pp(vm_obj const & ss, tactic_state const & ts) {
    return smt_state_to_format_core(ss, ts);
}

vm_obj smt_state_to_format(vm_obj const & ss, vm_obj const & ts) {
    LEAN_TACTIC_TRY;
    return to_obj(smt_state_to_format_core(ss, to_tactic_state(ts)));
    LEAN_TACTIC_CATCH(to_tactic_state(ts));
}

vm_obj mk_smt_state_empty_exception(tactic_state const & ts) {
    return mk_tactic_exception("tactic failed, smt_state is empty", ts);
}

vm_obj exact_core(expr const & e, vm_obj const & ss, tactic_state const & ts) {
    lean_assert(!is_nil(ss));
    lean_assert(ts.goals());
    vm_obj new_ss = tail(ss);
    auto mctx = ts.mctx();
    mctx.assign(head(ts.goals()), e);
    tactic_state new_ts = set_mctx_goals(ts, mctx, tail(ts.goals()));
    return mk_smt_tactic_success(new_ss, to_obj(new_ts));
}

vm_obj smt_tactic_close(vm_obj const & ss, vm_obj const & _ts) {
    tactic_state const & ts = to_tactic_state(_ts);
    LEAN_TACTIC_TRY;
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    expr target      = ts.get_main_goal_decl()->get_type();
    type_context ctx = mk_type_context_for(ts);
    smt_goal g       = to_smt_goal(head(ss));
    smt S(ctx, g);
    if (S.inconsistent()) {
        if (auto pr = S.get_inconsistency_proof()) {
            expr H      = mk_false_rec(ctx, target, *pr);
            return exact_core(H, ss, ts);
        }
    }

    S.internalize(target);
    expr lhs, rhs;
    if (is_eq(target, lhs, rhs)) {
        if (auto pr = S.get_eq_proof(lhs, rhs)) {
            return exact_core(*pr, ss, ts);
        }
    }

    if (auto pr = S.get_proof(target)) {
        return exact_core(*pr, ss, ts);
    }
    LEAN_TACTIC_CATCH(ts);
    return mk_tactic_exception("smt_tactic.close failed", ts);
}

vm_obj smt_tactic_intros_core(vm_obj const & use_unused_names, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = to_tactic_state(_ts);
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    LEAN_TACTIC_TRY;

    smt_goal new_sgoal   = to_smt_goal(head(ss));

    vm_obj r = preprocess(ts, new_sgoal.get_pre_config());
    if (is_tactic_result_exception(r)) return r;
    ts = to_tactic_state(get_tactic_result_state(r));

    metavar_context mctx = ts.mctx();
    expr new_mvar = intros(ts.env(), ts.get_options(), mctx, head(ts.goals()), new_sgoal,
                           to_bool(use_unused_names));

    tactic_state new_ts = set_mctx_goals(ts, mctx, cons(new_mvar, tail(ts.goals())));
    vm_obj new_ss    = mk_vm_cons(to_obj(new_sgoal), tail(ss));
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_state_classical(vm_obj const & ss) {
    bool r = false;
    if (!is_nil(ss)) {
        smt_goal const & g = to_smt_goal(head(ss));
        r = g.get_cc_state().get_config().m_em;
    }
    return mk_vm_bool(r);
}

vm_obj smt_tactic_ematch_core(vm_obj const & pred, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = to_tactic_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    expr target      = ts.get_main_goal_decl()->get_type();
    type_context ctx = mk_type_context_for(ts);
    smt_goal g       = to_smt_goal(head(ss));
    smt S(ctx, g);
    S.internalize(target);
    buffer<expr_pair> new_instances;
    S.ematch(new_instances);
    for (expr_pair const & p : new_instances) {
        expr type   = p.first;
        expr proof  = p.second;
        vm_obj keep = invoke(pred, to_obj(type));
        if (to_bool(keep)) {
            simp_result r = preprocess(ctx, g.get_pre_config(), type);
            // TODO(Leo): check if lemma is already known to be true, and discard
            if (r.has_proof()) {
                expr new_proof = mk_app(ctx, get_eq_mp_name(), r.get_proof(), proof);
                S.add(r.get_new(), new_proof);
            } else {
                // TODO(Leo): check if we need to use id_locked
                S.add(r.get_new(), proof);
            }
        }
    }
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_env_mctx(ts, ctx.env(), ctx.mctx());
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

void initialize_smt_state() {
    register_trace_class(name({"smt", "units"}));

    DECLARE_VM_BUILTIN(name({"smt_state", "mk"}),             smt_state_mk);
    DECLARE_VM_BUILTIN(name({"smt_state", "to_format"}),      smt_state_to_format);
    DECLARE_VM_BUILTIN(name({"smt_state", "classical"}),      smt_state_classical);
    DECLARE_VM_BUILTIN("tactic_to_smt_tactic",                tactic_to_smt_tactic);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "close"}),         smt_tactic_close);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intros_core"}),   smt_tactic_intros_core);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "ematch_core"}),   smt_tactic_ematch_core);
}

void finalize_smt_state() {
}
}
