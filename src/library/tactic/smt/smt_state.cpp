/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/delayed_abstraction.h"
#include "library/type_context.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/tactic/user_attribute.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/simplify.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/tactic/change_tactic.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/smt_state.h"

namespace lean {
smt_goal::smt_goal(smt_config_ref const & cfg):
    m_cc_state(cfg->m_ho_fns, cfg->m_cc_config),
    m_em_state(cfg->m_em_config, cfg->m_em_lemmas),
    m_cfg(cfg) {
}

smt_goal::smt_goal(smt_config const & cfg):
    smt_goal(std::make_shared<smt_config>(cfg)) {
}

smt::smt(type_context_old & ctx, defeq_can_state & dcs, smt_goal & g):
    m_ctx(ctx),
    m_dcs(dcs),
    m_goal(g),
    m_cc(ctx, m_goal.m_cc_state, dcs, this, this) {
}

smt::~smt() {
}

void smt::propagated(unsigned n, expr const * p) {
    lean_trace(name({"smt", "fact"}), scope_trace_env _(m_ctx.env(), m_ctx);
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
    m_cc.internalize(e, 0);
    m_goal.m_em_state.internalize(m_ctx, e);
}

void smt::new_aux_cc_term(expr const & e) {
    m_goal.m_em_state.internalize(m_ctx, e);
}

void smt::add(expr const & type, expr const & proof, unsigned gen) {
    m_goal.m_em_state.internalize(m_ctx, type);
    m_cc.add(type, proof, gen);
}

void smt::ematch(buffer<new_instance> & result) {
    ::lean::ematch(m_ctx, m_goal.m_em_state, m_cc, result);
}

void smt::ematch_using(hinst_lemma const & lemma, buffer<new_instance> & result) {
    ::lean::ematch(m_ctx, m_goal.m_em_state, m_cc, lemma, false, result);
}

static dsimplify_fn mk_dsimp(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg);

expr smt::normalize(expr const & e) {
    type_context_old::zeta_scope _1(m_ctx, m_goal.get_pre_config().m_zeta);
    dsimplify_fn dsimp       = mk_dsimp(m_ctx, m_dcs, m_goal.get_pre_config());
    return dsimp(e);
}

struct vm_smt_goal : public vm_external {
    smt_goal m_val;
    vm_smt_goal(smt_goal const & v):m_val(v) {}
    virtual ~vm_smt_goal() {}
    virtual void dealloc() override {
        this->~vm_smt_goal(); get_vm_allocator().deallocate(sizeof(vm_smt_goal), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_smt_goal(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_smt_goal))) vm_smt_goal(m_val); }
};

bool is_smt_goal(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_smt_goal*>(to_external(o));
}

smt_goal const & to_smt_goal(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_smt_goal*>(to_external(o)));
    return static_cast<vm_smt_goal*>(to_external(o))->m_val;
}

vm_obj to_obj(smt_goal const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_smt_goal))) vm_smt_goal(s));
}

vm_obj mk_smt_tactic_success(vm_obj const & a, vm_obj const & ss, vm_obj const & ts) {
    return tactic::mk_success(mk_vm_pair(a, ss), ts);
}

vm_obj mk_smt_tactic_success(vm_obj const & ss, vm_obj const & ts) {
    return mk_smt_tactic_success(mk_vm_unit(), ss, ts);
}

vm_obj mk_smt_tactic_success(vm_obj const & ss, tactic_state const & ts) {
    return mk_smt_tactic_success(ss, to_obj(ts));
}

vm_obj tactic_success_to_smt_tactic_success(vm_obj const & r, vm_obj const & ss) {
    return mk_smt_tactic_success(tactic::get_success_value(r), ss, tactic::get_success_state(r));
}

/* Remove auxiliary definitions introduced by the equation compiler.
   Reason: ematching will close the goal by instantiating them.
   Then later, the equation compiler will fail to eliminate this application
   using structural or well founded induction. */
static tactic_state clear_recs(tactic_state const & s) {
    lean_assert(s.goals());
    expr mvar                = head(s.goals());
    metavar_context mctx     = s.mctx();
    expr new_mvar            = clear_recs(mctx, mvar);
    if (new_mvar == mvar)
        return s;
    else
        return set_mctx_goals(s, mctx, cons(new_mvar, tail(s.goals())));
}

static optional<local_instance> get_last_local_instance(local_context const & lctx) {
    if (optional<local_instances> const & lis = lctx.get_frozen_local_instances()) {
        if (*lis)
            return optional<local_instance>(head(*lis));
    }
    return optional<local_instance>();
}

static pair<tactic_state, unsigned> revert_all(tactic_state const & s) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    local_context lctx       = g->get_context();
    buffer<expr> hs;
    if (optional<local_instance> const & last_local_inst = get_last_local_instance(lctx)) {
        /* We should not revert local instances. */
        local_decl const & last_local_inst_decl = lctx.get_local_decl(mlocal_name(last_local_inst->get_local()));
        lctx.for_each_after(last_local_inst_decl, [&](local_decl const & d) { hs.push_back(d.mk_ref()); });
    } else {
        lctx.for_each([&](local_decl const & d) { hs.push_back(d.mk_ref()); });
    }
    bool preserve_to_revert_order = false;
    tactic_state new_s = revert(hs, s, preserve_to_revert_order);
    return mk_pair(new_s, hs.size());
}

static dsimplify_fn mk_dsimp(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg) {
    dsimp_config dcfg;
    dcfg.m_max_steps          = cfg.m_max_steps;
    dcfg.m_canonize_instances = false;
    /* We use eta reduction to make sure terms such as (fun x, list x) are reduced to list.

       Given (a : nat) (l : list nat) (a ∈ a::l), the elaborator produces

              @mem nat list (@list.has_mem nat) a (a::l)

       On the other hand, it elaborates (λ (α : Type u) (l : list α) (a : α), a ∈ l) as

             (λ (α : Type u) (l : list α) (a : α), @mem α (λ (α : Type u), list α) (@list.has_mem α) a l)

       Another option is to use eta expansion. When we have metavariables, eta expansion is a better option.
       Example:  (fun x, ?m)  =?= f
       To solve this unification problem, we need to eta expand.

       This is not an issue in this module since it assumes goals do not contain metavariables.
    */
    dcfg.m_eta               = true;
    simp_lemmas_for eq_lemmas;
    if (auto r = cfg.m_simp_lemmas.find(get_eq_name()))
        eq_lemmas = *r;
    return dsimplify_fn(ctx, dcs, eq_lemmas, list<name>(), dcfg);
}

static simplify_fn mk_simp(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg) {
    simp_config scfg;
    scfg.m_max_steps          = cfg.m_max_steps;
    scfg.m_contextual         = false;
    scfg.m_lift_eq            = true;
    scfg.m_canonize_instances = true;
    scfg.m_canonize_proofs    = false;
    scfg.m_use_axioms         = true;
    scfg.m_zeta               = cfg.m_zeta;
    return simplify_fn(ctx, dcs, cfg.m_simp_lemmas, list<name>(), scfg);
}

static simp_result preprocess(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg, expr const & e) {
    type_context_old::zeta_scope         scope1(ctx, cfg.m_zeta);
    type_context_old::transparency_scope scope2(ctx, transparency_mode::Reducible);
    dsimplify_fn dsimp       = mk_dsimp(ctx, dcs, cfg);
    expr new_e               = dsimp(e);
    simplify_fn simp         = mk_simp(ctx, dcs, cfg);
    simp_result r            = simp(get_eq_name(), new_e);
    return r;
}

static vm_obj preprocess(tactic_state s, smt_pre_config const & cfg) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    type_context_old ctx         = mk_type_context_for(s, transparency_mode::Reducible);
    expr target              = g->get_type();
    defeq_can_state dcs      = s.dcs();
    simp_result r            = preprocess(ctx, dcs, cfg, target);
    if (!r.has_proof()) {
        tactic_state new_s = set_dcs(s, dcs);
        return change(r.get_new(), new_s);
    } else {
        expr new_M           = ctx.mk_metavar_decl(ctx.lctx(), r.get_new());
        expr h               = mk_eq_mpr(ctx, r.get_proof(), new_M);
        metavar_context mctx = ctx.mctx();
        mctx.assign(head(s.goals()), h);
        tactic_state new_s   = set_mctx_goals_dcs(s, mctx, cons(new_M, tail(s.goals())), dcs);
        return tactic::mk_success(new_s);
    }
}

static expr_pair preprocess_forward(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg, expr const & type, expr const & h) {
    simp_result r = preprocess(ctx, dcs, cfg, type);
    if (r.has_proof()) {
        expr new_h = mk_eq_mp(ctx, r.get_proof(), h);
        return mk_pair(r.get_new(), new_h);
    } else if (r.get_new() == type) {
        return mk_pair(type, h);
    } else {
        return mk_pair(r.get_new(), mk_id(ctx, r.get_new(), h));
    }
}

static expr_pair preprocess_forward(type_context_old & ctx, defeq_can_state & dcs, smt_goal const & g, expr const & type, expr const & h) {
    return preprocess_forward(ctx, dcs, g.get_pre_config(), type, h);
}

static name mk_intro_name(type_context_old & ctx, name const & bname, bool use_unused_names, list<name> & user_ids) {
    if (user_ids) {
        name r   = head(user_ids);
        user_ids = tail(user_ids);
        return r;
    } else if (use_unused_names) {
        return ctx.get_unused_name(bname);
    } else {
        return bname;
    }
}

/* This try_to_pi version only unfolds the head symbol if it is a not-application or a reducible constant. */
static expr convervative_try_to_pi(type_context_old & ctx, expr const & e) {
    expr new_e = ctx.whnf_head_pred(e, [&](expr const & t) {
            if (is_not(t)) return true;
            expr const & fn = get_app_fn(e);
            return is_constant(fn) && is_reducible(ctx.env(), const_name(fn));
        });
    return is_pi(new_e) ? new_e : e;
}

static expr intros(environment const & env, options const & opts, metavar_context & mctx, expr const & mvar,
                   defeq_can_state & dcs, smt_goal & s_goal, bool use_unused_names,
                   optional<unsigned> const & num, list<name> ids) {
    optional<metavar_decl> decl = mctx.find_metavar_decl(mvar);
    lean_assert(decl);
    type_context_old ctx(env, opts, mctx, decl->get_context(), transparency_mode::Semireducible);
    smt S(ctx, dcs, s_goal);
    /* We need to use dsimp to canonize instances as we introduce hypotheses.
       Example: suppose we are introducing
         forall {α : Type u} [field α] (x y : α), f (x + y) (y + x) (x + y) = 0

       The nested instances of has_add and has_zero must be canonized and registered at dcs.
    */
    dsimplify_fn dsimp = mk_dsimp(ctx, dcs, s_goal.get_pre_config());
    type_context_old::zeta_scope _1(ctx, s_goal.get_pre_config().m_zeta);
    expr target = decl->get_type();
    type_context_old::tmp_locals locals(ctx);
    buffer<expr> new_Hs;
    buffer<expr> to_inst;
    for (unsigned i = 0; !num || i < *num; i++) {
        if (!is_pi(target) && !is_let(target)) {
            target = instantiate_rev(target, to_inst.size(), to_inst.data());
            to_inst.clear();
            if (!num) {
                target = convervative_try_to_pi(ctx, target);
            } else {
                target = ctx.relaxed_try_to_pi(target);
            }
        }
        if (is_pi(target)) {
            expr type = dsimp(instantiate_rev(binding_domain(target), to_inst.size(), to_inst.data()));
            name n    = mk_intro_name(ctx, binding_name(target), use_unused_names, ids);
            expr h    = locals.push_local(n, type);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(h);
            S.add(type, h);
            lean_trace(name({"smt", "intro"}), scope_trace_env _(env, ctx);
                       tout() << n << " : " << type << "\n";);
            target = binding_body(target);
        } else if (is_let(target)) {
            expr type  = dsimp(instantiate_rev(let_type(target), to_inst.size(), to_inst.data()));
            expr value = dsimp(instantiate_rev(let_value(target), to_inst.size(), to_inst.data()));
            name n     = mk_intro_name(ctx, let_name(target), use_unused_names, ids);
            expr h     = locals.push_let(n, type, value);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(type);
            S.internalize(value);
            S.add(type, h);
            lean_trace(name({"smt", "intro"}), scope_trace_env _(env, ctx);
                       tout() << n << " : " << type << "\n";);
            target = let_body(target);
        } else {
            break;
        }
    }
    target = dsimp(instantiate_rev(target, to_inst.size(), to_inst.data()));

    expr new_M   = ctx.mk_metavar_decl(ctx.lctx(), target);
    expr new_val = abstract_locals(mk_delayed_abstraction_with_locals(new_M, new_Hs), new_Hs.size(), new_Hs.data());
    unsigned i   = new_Hs.size();
    while (i > 0) {
        --i;
        local_decl d = ctx.lctx().get_local_decl(new_Hs[i]);
        expr type = d.get_type();
        type      = abstract_locals(type, i, new_Hs.data());
        if (auto letval = d.get_value()) {
            letval    = abstract_locals(*letval, i, new_Hs.data());
            new_val   = mk_let(d.get_pp_name(), type, *letval, new_val);
        } else {
            new_val   = mk_lambda(d.get_pp_name(), type, new_val, d.get_info());
        }
    }
    lean_assert(!ctx.mctx().is_assigned(new_M));
    mctx = ctx.mctx();
    mctx.assign(mvar, new_val);
    return new_M;
}

/* Assert lemma in the current state if does not have universal metavariables, and return true.
   Return false otherwise. */
static bool add_em_fact(smt & S, type_context_old & ctx, hinst_lemma const & lemma) {
    if (lemma.m_num_mvars == 0 && lemma.m_num_uvars == 0) {
        expr type  = lemma.m_prop;
        expr h     = lemma.m_proof;
        std::tie(type, h) = preprocess_forward(ctx, S.dcs(), S.get_pre_config(), type, h);
        lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                   tout() << "new ground fact: " << type << "\n";);
        S.add(type, h);
        return true;
    } else {
        return false;
    }
}

tactic_state add_em_facts(tactic_state const & ts, smt_goal & g) {
    type_context_old ctx      = mk_type_context_for(ts);
    defeq_can_state dcs   = ts.dcs();
    smt S(ctx, dcs, g);
    hinst_lemmas lemmas   = g.get_em_state().get_new_lemmas();
    lemmas.for_each([&](hinst_lemma const & lemma) {
            add_em_fact(S, ctx, lemma);
        });
    return set_dcs(ts, dcs);
}

vm_obj mk_smt_state(tactic_state s, smt_config const & cfg) {
    if (!s.goals()) return mk_no_goals_exception(s);
    unsigned num_reverted;
    /* Remark: revert_all only reverts declarations after the last local instance.

       It is not reliable to implement "revert/do something/intro" idiom using `num_reverted`.
       The problem is that the `do something` step may eliminate `let`-decls.
       We have to figure out a way to do it more reliably.
    */
    std::tie(s, num_reverted) = revert_all(clear_recs(s));
    smt_goal new_goal(cfg);

    vm_obj r = preprocess(s, cfg.m_pre_config);
    if (tactic::is_result_exception(r)) return r;
    s = tactic::to_state(tactic::get_success_state(r));

    metavar_context mctx = s.mctx();
    bool use_unused_names = true;
    defeq_can_state dcs = s.dcs();
    list<name> ids;
    expr new_M = intros(s.env(), s.get_options(), mctx, head(s.goals()), dcs, new_goal, use_unused_names,
                        optional<unsigned>(num_reverted), ids);

    s = set_mctx_goals_dcs(s, mctx, cons(new_M, tail(s.goals())), dcs);
    s = add_em_facts(s, new_goal);

    return tactic::mk_success(mk_vm_cons(to_obj(new_goal), mk_vm_nil()), s);
}

/* TODO(Leo): for hinst_lemma sets, the attribute name and declaration name should be the same. */

static hinst_lemmas get_hinst_lemmas(name const & attr_name, tactic_state const & s) {
    auto & S      = get_vm_state();
    vm_obj r      = user_attribute_get_cache(S, s, attr_name);
    if (tactic::is_result_exception(r))
        throw exception(sstream() << "failed to initialize smt_state, failed to retrieve attribute '" << attr_name << "'");
    vm_obj lemmas = tactic::get_success_value(r);
    if (!is_hinst_lemmas(lemmas))
        throw exception(sstream() << "failed to initialize smt_state, attribute '" << attr_name << "' is not a hinst_lemmas");
    return to_hinst_lemmas(lemmas);
}

static simp_lemmas get_simp_lemmas(name const & attr_name, tactic_state const & s) {
    auto & S      = get_vm_state();
    vm_obj r      = user_attribute_get_cache(S, s, mk_simp_attr_decl_name(attr_name));
    if (tactic::is_result_exception(r))
        throw exception(sstream() << "failed to initialize smt_state, failed to retrieve attribute '" << attr_name << "'");
    vm_obj lemmas = tactic::get_success_value(r);
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
    r.m_simp_attr     = to_name(cfield(cfg, 0));
    r.m_simp_lemmas   = get_simp_lemmas(r.m_simp_attr, s);
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
    r.m_em_attr                         = to_name(cfield(cfg, 3));
    r.m_em_lemmas                       = get_hinst_lemmas(r.m_em_attr, s);
    return r;
}

vm_obj smt_state_mk(vm_obj const & cfg, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return mk_smt_state(tactic::to_state(s), to_smt_config(cfg, tactic::to_state(s)));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

bool same_hyps(metavar_context const & mctx, expr const & mvar1, expr const & mvar2) {
    lean_assert(is_metavar(mvar1));
    lean_assert(is_metavar(mvar2));
    optional<metavar_decl> d1 = mctx.find_metavar_decl(mvar1);
    optional<metavar_decl> d2 = mctx.find_metavar_decl(mvar2);
    return d1 && d2 && equal_locals(d1->get_context(), d2->get_context());
}

vm_obj tactic_to_smt_tactic(vm_obj const &, vm_obj const & tac, vm_obj const & ss, vm_obj const & ts) {
    vm_obj r1 = invoke(tac, ts);
    if (tactic::is_result_exception(r1)) {
        /* Tactic failed */
        return r1;
    }
    if (is_nil(ss)) {
        /* There is no SMT state associated with any goal. */
        return tactic_success_to_smt_tactic_success(r1, ss);
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
    vm_obj new_ts = tactic::get_success_state(r1);
    if (is_eqp(tactic::to_state(ts), tactic::to_state(new_ts))) {
        /* The tactic_state was not modified */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    list<expr> goals          = tactic::to_state(ts).goals();
    list<expr> new_goals      = tactic::to_state(new_ts).goals();
    if (goals == new_goals) {
        /* Set of goals did not change. */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    if (!new_goals) {
        /* There are no new goals */
        return tactic_success_to_smt_tactic_success(r1, mk_vm_nil());
    }
    if (!goals) {
        return tactic::mk_exception("failed to lift tactic to smt_tactic, there were no goals to be solved", tactic::to_state(ts));
    }
    if (new_goals == tail(goals)) {
        /* Main goal was solved */
        /* remove one SMT goal */
        vm_obj new_ss = tail(ss);
        return tactic_success_to_smt_tactic_success(r1, new_ss);
    }
    metavar_context const & mctx = tactic::to_state(new_ts).mctx();
    if (tail(new_goals) == tail(goals) && same_hyps(mctx, head(new_goals), head(goals))) {
        /* The set of hypotheses in the main goal did not change */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    vm_obj new_ss = ss;
    while (true) {
        if (!same_hyps(mctx, head(new_goals), head(goals))) {
            return tactic::mk_exception("failed to lift tactic to smt_tactic, set of hypotheses has been modified, at least one of the used tactics has to be lifted manually",
                                       tactic::to_state(ts));
        }
        if (tail(new_goals) == tail(goals)) {
            return tactic_success_to_smt_tactic_success(r1, new_ss);
        }
        /* copy smt state */
        new_ss = mk_vm_cons(head(new_ss), new_ss);

        /* Move to next */
        new_goals = tail(new_goals);
        if (!new_goals) {
            return tactic::mk_exception("failed to lift tactic to smt_tactic, only tactics that modify a prefix of the list of goals can be automatically lifted",
                                       tactic::to_state(ts));
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
            format fmt_it = fmt(it);
            if (is_pi(it) || is_lambda(it) || is_let(it))
                fmt_it = paren(fmt_it);
            if (r)
                r = *r + comma() + line() + fmt_it;
            else
                r = fmt_it;
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

static format pp_equivalences(type_context_old & ctx, cc_state const & ccs, formatter const & fmt) {
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
    bool inst_mvars            = get_pp_instantiate_mvars(opts);
    bool unicode               = get_pp_unicode(opts);
    unsigned indent            = get_pp_indent(opts);
    metavar_decl decl          = *ts.get_main_goal_decl();
    local_context lctx         = decl.get_context();
    metavar_context mctx_tmp   = ts.mctx();
    expr target                = decl.get_type();
    if (inst_mvars)
        target                 = mctx_tmp.instantiate_mvars(target);
    format turnstile(unicode ? "⊢" : "|-");
    type_context_old ctx(ts.env(), opts, mctx_tmp, lctx, transparency_mode::All);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt              = fmtf(ts.env(), opts, ctx);
    defeq_can_state dcs        = ts.dcs();
    smt S(ctx, dcs, sg);
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
    format turnstile(unicode ? "⊢" : "|-");
    for (expr const & g : tail(ts.goals())) {
        metavar_decl d = mctx.get_metavar_decl(g);
        type_context_old ctx(ts.env(), ts.get_options(), mctx, d.get_context(), transparency_mode::Semireducible);
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
    return to_obj(smt_state_to_format_core(ss, tactic::to_state(ts)));
    LEAN_TACTIC_CATCH(tactic::to_state(ts));
}

vm_obj mk_smt_state_empty_exception(tactic_state const & ts) {
    return tactic::mk_exception("tactic failed, smt_state is empty", ts);
}

vm_obj mk_smt_state_empty_exception(vm_obj const & ts) {
    lean_assert(tactic::is_state(ts));
    return mk_smt_state_empty_exception(tactic::to_state(ts));
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
    tactic_state const & ts = tactic::to_state(_ts);
    LEAN_TACTIC_TRY;
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    expr target         = ts.get_main_goal_decl()->get_type();
    type_context_old ctx    = mk_type_context_for(ts);
    smt_goal g          = to_smt_goal(head(ss));
    defeq_can_state dcs = ts.dcs();
    smt S(ctx, dcs, g);
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
    return tactic::mk_exception("smt_tactic.close failed", ts);
}

vm_obj smt_tactic_intros_core(list<name> const & ids, optional<unsigned> const & num, vm_obj const & ss, tactic_state ts) {
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    LEAN_TACTIC_TRY;

    smt_goal new_sgoal   = to_smt_goal(head(ss));

    vm_obj r = preprocess(ts, new_sgoal.get_pre_config());
    if (tactic::is_result_exception(r)) return r;
    ts = tactic::to_state(tactic::get_success_state(r));

    metavar_context mctx = ts.mctx();
    defeq_can_state dcs  = ts.dcs();
    expr new_mvar = intros(ts.env(), ts.get_options(), mctx, head(ts.goals()),
                           dcs, new_sgoal, true, num, ids);

    tactic_state new_ts = set_mctx_goals_dcs(ts, mctx, cons(new_mvar, tail(ts.goals())), dcs);
    vm_obj new_ss       = mk_vm_cons(to_obj(new_sgoal), tail(ss));
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_intros(vm_obj const & ss, vm_obj const & ts) {
    return smt_tactic_intros_core(list<name>(), optional<unsigned>(), ss, tactic::to_state(ts));
}

vm_obj smt_tactic_intron(vm_obj const & n, vm_obj const & ss, vm_obj const & ts) {
    return smt_tactic_intros_core(list<name>(), optional<unsigned>(force_to_unsigned(n)), ss, tactic::to_state(ts));
}

vm_obj smt_tactic_intro_lst(vm_obj const & _ids, vm_obj const & ss, vm_obj const & ts) {
    list<name> const & ids = to_list_name(_ids);
    return smt_tactic_intros_core(list<name>(ids), optional<unsigned>(length(ids)), ss, tactic::to_state(ts));
}

vm_obj smt_tactic_intros_core(vm_obj const & _ids, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    LEAN_TACTIC_TRY;

    smt_goal new_sgoal   = to_smt_goal(head(ss));

    vm_obj r = preprocess(ts, new_sgoal.get_pre_config());
    if (tactic::is_result_exception(r)) return r;
    ts = tactic::to_state(tactic::get_success_state(r));

    metavar_context mctx = ts.mctx();
    defeq_can_state dcs  = ts.dcs();
    list<name> ids       = to_list_name(_ids);
    optional<unsigned> n;
    if (ids) n = length(ids);
    expr new_mvar = intros(ts.env(), ts.get_options(), mctx, head(ts.goals()),
                           dcs, new_sgoal, true, n, ids);

    tactic_state new_ts = set_mctx_goals_dcs(ts, mctx, cons(new_mvar, tail(ts.goals())), dcs);
    vm_obj new_ss       = mk_vm_cons(to_obj(new_sgoal), tail(ss));
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
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    expr target         = ts.get_main_goal_decl()->get_type();
    type_context_old ctx    = mk_type_context_for(ts);
    defeq_can_state dcs = ts.dcs();
    smt_goal g          = to_smt_goal(head(ss));
    smt S(ctx, dcs, g);
    S.internalize(target);
    buffer<new_instance> new_instances;
    S.ematch(new_instances);
    if (new_instances.empty())
        return tactic::mk_exception("ematch failed, no new instance was produced", ts);
    for (new_instance const & p : new_instances) {
        expr type   = p.m_instance;
        expr proof  = p.m_proof;
        vm_obj keep = invoke(pred, to_obj(type));
        if (to_bool(keep)) {
            std::tie(type, proof) = preprocess_forward(ctx, dcs, g, type, proof);
            lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                       tout() << "instance, generation: " << p.m_generation << ", after preprocessing\n"
                       << type << "\n";);
            S.add(type, proof, p.m_generation);
        }
    }
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_mk_ematch_eqn_lemmas_for_core(vm_obj const & md, vm_obj const & decl_name, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(ts);
    buffer<name> eqns;
    get_ext_eqn_lemmas_for(ts.env(), to_name(decl_name), eqns);
    if (eqns.empty())
        return tactic::mk_exception(sstream() << "tactic failed, '" << to_name(decl_name) << "' does not have equation lemmas", ts);
    hinst_lemmas hs;
    for (name const & eqn : eqns) {
        declaration eqn_decl = ctx.env().get(eqn);
        hinst_lemma h = mk_hinst_lemma(ctx, to_transparency_mode(md), eqn, true);
        hs.insert(h);
    }
    tactic_state new_ts = set_env_mctx(ts, ctx.env(), ctx.mctx());
    return mk_smt_tactic_success(to_obj(hs), ss, to_obj(new_ts));
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_to_cc_state(vm_obj const & ss, vm_obj const & ts) {
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    return mk_smt_tactic_success(to_obj(to_smt_goal(head(ss)).get_cc_state()), ss, ts);
}

vm_obj smt_tactic_to_em_state(vm_obj const & ss, vm_obj const & ts) {
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    return mk_smt_tactic_success(to_obj(to_smt_goal(head(ss)).get_em_state()), ss, ts);
}

vm_obj smt_tactic_preprocess(vm_obj const & e, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(ts);
    smt_goal g          = to_smt_goal(head(ss));
    defeq_can_state dcs = ts.dcs();
    simp_result r       = preprocess(ctx, dcs, g.get_pre_config(), to_expr(e));
    r                   = finalize(ctx, get_eq_name(), r);
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(mk_vm_pair(to_obj(r.get_new()), to_obj(r.get_proof())), ss, to_obj(new_ts));
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_get_lemmas(vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    smt_goal g      = to_smt_goal(head(ss));
    hinst_lemmas s  = g.get_em_state().get_lemmas();
    s.merge(g.get_em_state().get_new_lemmas());
    vm_obj r        = to_obj(s);
    return mk_smt_tactic_success(r, ss, _ts);
}

vm_obj smt_tactic_set_lemmas(vm_obj const & lemmas, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts     = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    smt_goal g          = to_smt_goal(head(ss));
    g.set_lemmas(to_hinst_lemmas(lemmas));
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    return mk_smt_tactic_success(new_ss, _ts);
}

vm_obj smt_tactic_add_lemmas(vm_obj const & lemmas, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts     = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    type_context_old ctx    = mk_type_context_for(ts);
    defeq_can_state dcs = ts.dcs();
    smt_goal g          = to_smt_goal(head(ss));
    smt S(ctx, dcs, g);
    to_hinst_lemmas(lemmas).for_each([&](hinst_lemma const & lemma) {
            bool is_fact = add_em_fact(S, ctx, lemma);
            if (!is_fact) {
                lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                           tout() << "new equation lemma " << lemma << "\n" << lemma.m_prop << "\n";);
                g.add_lemma(lemma);
            }
        });
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(new_ss, new_ts);
}

vm_obj smt_tactic_ematch_using(vm_obj const & hs, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    expr target         = ts.get_main_goal_decl()->get_type();
    type_context_old ctx    = mk_type_context_for(ts);
    defeq_can_state dcs = ts.dcs();
    smt_goal g          = to_smt_goal(head(ss));
    smt S(ctx, dcs, g);
    S.internalize(target);
    bool added_facts = false;
    buffer<new_instance> new_instances;
    to_hinst_lemmas(hs).for_each([&](hinst_lemma const & lemma) {
            if (add_em_fact(S, ctx, lemma)) {
                added_facts = true;
            } else {
                S.ematch_using(lemma, new_instances);
            }
        });
    if (!added_facts && new_instances.empty())
        return tactic::mk_exception("ematch_using failed, no instance was produced", ts);
    for (new_instance const & p : new_instances) {
        expr type   = p.m_instance;
        expr proof  = p.m_proof;
        std::tie(type, proof) = preprocess_forward(ctx, dcs, g, type, proof);
        lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                   tout() << "instance, generation: " << p.m_generation
                   << ", after preprocessing\n" << type << "\n";);
        S.add(type, proof, p.m_generation);
    }
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

/*
structure smt_pre_config :=
(simp_attr : name := `pre_smt)
(max_steps : nat  := 1000000)
(zeta      : bool := ff)

structure smt_config :=
(cc_cfg        : cc_config      := {})
(em_cfg        : ematch_config  := {})
(pre_cfg       : smt_pre_config := {})
(em_attr       : name           := `ematch)
*/
vm_obj smt_tactic_get_config(vm_obj const & ss, vm_obj const & ts) {
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    smt_goal g = to_smt_goal(head(ss));
    smt_config const & cfg = g.get_config();
    smt_pre_config const & pre = g.get_pre_config();

    vm_obj cc_cfg  = g.get_cc_state().mk_vm_cc_config();
    vm_obj em_cfg  = g.get_em_state().mk_vm_ematch_config();
    vm_obj pre_cfg = mk_vm_constructor(0, to_obj(pre.m_simp_attr), mk_vm_nat(pre.m_max_steps), mk_vm_bool(pre.m_zeta));
    vm_obj em_attr = to_obj(cfg.m_em_attr);

    vm_obj r = mk_vm_constructor(0, cc_cfg, em_cfg, pre_cfg, em_attr);

    return mk_smt_tactic_success(r, ss, ts);
}

void initialize_smt_state() {
    register_trace_class("smt");
    register_trace_class(name({"smt", "fact"}));
    register_trace_class(name({"smt", "intro"}));
    register_trace_class(name({"smt", "ematch"}));

    DECLARE_VM_BUILTIN(name({"smt_state", "mk"}),                                smt_state_mk);
    DECLARE_VM_BUILTIN(name({"smt_state", "to_format"}),                         smt_state_to_format);
    DECLARE_VM_BUILTIN(name({"smt_state", "classical"}),                         smt_state_classical);
    DECLARE_VM_BUILTIN("tactic_to_smt_tactic",                                   tactic_to_smt_tactic);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "close"}),                            smt_tactic_close);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intros"}),                           smt_tactic_intros);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intron"}),                           smt_tactic_intron);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intro_lst"}),                        smt_tactic_intro_lst);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "ematch_core"}),                      smt_tactic_ematch_core);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "ematch_using"}),                     smt_tactic_ematch_using);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "to_cc_state"}),                      smt_tactic_to_cc_state);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "to_em_state"}),                      smt_tactic_to_em_state);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "get_config"}),                       smt_tactic_get_config);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "preprocess"}),                       smt_tactic_preprocess);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "get_lemmas"}),                       smt_tactic_get_lemmas);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "set_lemmas"}),                       smt_tactic_set_lemmas);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "add_lemmas"}),                       smt_tactic_add_lemmas);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "mk_ematch_eqn_lemmas_for_core"}),    smt_tactic_mk_ematch_eqn_lemmas_for_core);
}

void finalize_smt_state() {
}
}
