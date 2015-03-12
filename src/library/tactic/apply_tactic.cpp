/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/error_msgs.h"
#include "kernel/type_checker.h"
#include "library/reducible.h"
#include "library/kernel_bindings.h"
#include "library/unifier.h"
#include "library/occurs.h"
#include "library/constants.h"
#include "library/metavar_closure.h"
#include "library/type_util.h"
#include "library/local_context.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/class_instance_synth.h"

#ifndef LEAN_DEFAULT_APPLY_CLASS_INSTANCE
#define LEAN_DEFAULT_APPLY_CLASS_INSTANCE true
#endif

namespace lean {
static name * g_apply_class_instance = nullptr;
bool get_apply_class_instance(options const & opts) {
    return opts.get_bool(*g_apply_class_instance, LEAN_DEFAULT_APPLY_CLASS_INSTANCE);
}

/**
    \brief Given a sequence metas: <tt>(?m_1 ...) (?m_2 ... ) ... (?m_k ...)</tt>,
    we say ?m_i is "redundant" if it occurs in the type of some ?m_j.
    This procedure removes from metas any redundant element.
*/
static void remove_redundant_metas(buffer<expr> & metas) {
    buffer<expr> mvars;
    for (expr const & m : metas)
        mvars.push_back(get_app_fn(m));
    unsigned k = 0;
    for (unsigned i = 0; i < metas.size(); i++) {
        bool found = false;
        for (unsigned j = 0; j < metas.size(); j++) {
            if (j != i) {
                if (occurs(mvars[i], mlocal_type(mvars[j]))) {
                    found = true;
                    break;
                }
            }
        }
        if (!found) {
            metas[k] = metas[i];
            k++;
        }
    }
    metas.shrink(k);
}

enum subgoals_action_kind { IgnoreSubgoals, AddRevSubgoals, AddSubgoals, AddAllSubgoals };



static proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s,
                                         expr const & _e, buffer<constraint> & cs,
                                         bool add_meta, subgoals_action_kind subgoals_action) {
    goals const & gs = s.get_goals();
    if (empty(gs)) {
        throw_no_goal_if_enabled(s);
        return proof_state_seq();
    }
    bool class_inst   = get_apply_class_instance(ios.get_options());
    name_generator ngen = s.get_ngen();
    bool relax_opaque = s.relax_main_opaque();
    std::shared_ptr<type_checker> tc(mk_type_checker(env, ngen.mk_child(), relax_opaque));
    goal  g           = head(gs);
    goals tail_gs     = tail(gs);
    expr  t           = g.get_type();
    expr  e           = _e;
    auto e_t_cs       = tc->infer(e);
    e_t_cs.second.linearize(cs);
    expr  e_t         = e_t_cs.first;
    buffer<expr> metas;
    local_context ctx;
    bool initialized_ctx = false;
    unifier_config cfg(ios.get_options());
    if (add_meta) {
        // unsigned num_t   = get_expect_num_args(*tc, t);
        unsigned num_e_t = get_expect_num_args(*tc, e_t);
        // Remark: we used to add (num_e_t - num_t) arguments.
        // This would allow us to handle (A -> B) without using intros,
        // but it was preventing us from solving other problems
        for (unsigned i = 0; i < num_e_t; i++) {
            auto e_t_cs = tc->whnf(e_t);
            e_t_cs.second.linearize(cs);
            e_t        = e_t_cs.first;
            expr meta;
            if (class_inst && binding_info(e_t).is_inst_implicit()) {
                if (!initialized_ctx) {
                    ctx = g.to_local_context();
                    initialized_ctx = true;
                }
                bool use_local_insts = true;
                bool is_strict       = false;
                auto mc = mk_class_instance_elaborator(
                    env, ios, ctx, ngen.next(), optional<name>(),
                    relax_opaque, use_local_insts, is_strict,
                    some_expr(binding_domain(e_t)), e.get_tag(), cfg, nullptr);
                meta    = mc.first;
                cs.push_back(mc.second);
            } else {
                meta  = g.mk_meta(ngen.next(), binding_domain(e_t));
            }
            e          = mk_app(e, meta);
            e_t        = instantiate(binding_body(e_t), meta);
            metas.push_back(meta);
        }
    }
    metavar_closure cls(t);
    cls.mk_constraints(s.get_subst(), justification(), relax_opaque);
    pair<bool, constraint_seq> dcs = tc->is_def_eq(t, e_t);
    if (!dcs.first) {
        throw_tactic_exception_if_enabled(s, [=](formatter const & fmt) {
                format r = format("invalid 'apply' tactic, failed to unify");
                r       += pp_indent_expr(fmt, t);
                r       += compose(line(), format("with"));
                r       += pp_indent_expr(fmt, e_t);
                return r;
            });
        return proof_state_seq();
    }
    dcs.second.linearize(cs);
    unify_result_seq rseq = unify(env, cs.size(), cs.data(), ngen.mk_child(), s.get_subst(), cfg);
    list<expr> meta_lst   = to_list(metas.begin(), metas.end());
    return map2<proof_state>(rseq, [=](pair<substitution, constraints> const & p) -> proof_state {
            substitution const & subst    = p.first;
            constraints const & postponed = p.second;
            name_generator new_ngen(ngen);
            substitution new_subst = subst;
            expr new_e = new_subst.instantiate_all(e);
            assign(new_subst, g, new_e);
            goals new_gs = tail_gs;
            if (subgoals_action != IgnoreSubgoals) {
                buffer<expr> metas;
                for (auto m : meta_lst) {
                    if (!new_subst.is_assigned(get_app_fn(m)))
                        metas.push_back(m);
                }
                if (subgoals_action == AddRevSubgoals) {
                    for (unsigned i = 0; i < metas.size(); i++)
                        new_gs = cons(goal(metas[i], new_subst.instantiate_all(tc->infer(metas[i]).first)), new_gs);
                } else {
                    lean_assert(subgoals_action == AddSubgoals || subgoals_action == AddAllSubgoals);
                    if (subgoals_action == AddSubgoals)
                        remove_redundant_metas(metas);
                    unsigned i = metas.size();
                    while (i > 0) {
                        --i;
                        new_gs = cons(goal(metas[i], new_subst.instantiate_all(tc->infer(metas[i]).first)), new_gs);
                    }
                }
            }
            return proof_state(s, new_gs, new_subst, new_ngen, postponed);
        });
}

static proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s, expr const & e,
                                         bool add_meta, subgoals_action_kind subgoals_action) {
    buffer<constraint> cs;
    return apply_tactic_core(env, ios, s, e, cs, add_meta, subgoals_action);
}

tactic eassumption_tactic() {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return proof_state_seq();
            }
            proof_state new_s = s.update_report_failure(false);
            proof_state_seq r;
            goal g = head(gs);
            buffer<expr> hs;
            get_app_args(g.get_meta(), hs);
            for (expr const & h : hs) {
                r = append(r, apply_tactic_core(env, ios, new_s, h, false, IgnoreSubgoals));
            }
            return r;
        });
}

tactic apply_tactic_core(elaborate_fn const & elab, expr const & e, subgoals_action_kind k) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return proof_state_seq();
            }
            goal const & g      = head(gs);
            name_generator ngen = s.get_ngen();
            expr       new_e;
            buffer<constraint> cs;
            auto ecs = elab(g, ngen.mk_child(), e, none_expr(), false);
            new_e    = ecs.first;
            to_buffer(ecs.second, cs);
            to_buffer(s.get_postponed(), cs);
            proof_state new_s(s, ngen, constraints());
            return apply_tactic_core(env, ios, new_s, new_e, cs, true, k);
        });
}

tactic apply_tactic(elaborate_fn const & elab, expr const & e) {
    return apply_tactic_core(elab, e, AddSubgoals);
}

tactic fapply_tactic(elaborate_fn const & elab, expr const & e) {
    return apply_tactic_core(elab, e, AddAllSubgoals);
}

tactic rapply_tactic(elaborate_fn const & elab, expr const & e) {
    return apply_tactic_core(elab, e, AddRevSubgoals);
}

int mk_eassumption_tactic(lua_State * L) { return push_tactic(L, eassumption_tactic()); }
void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_eassumption_tactic, "eassumption_tac");
}

void initialize_apply_tactic() {
    g_apply_class_instance = new name{"apply", "class_instance"};
    register_bool_option(*g_apply_class_instance, LEAN_DEFAULT_APPLY_CLASS_INSTANCE,
                         "(apply tactic) if true apply tactic uses class-instances "
                         "resolution for instance implicit arguments");

    register_tac(get_tactic_apply_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'apply' tactic, invalid argument");
                     return apply_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });

    register_tac(get_tactic_rapply_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'rapply' tactic, invalid argument");
                     return rapply_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });

    register_tac(get_tactic_fapply_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'fapply' tactic, invalid argument");
                     return fapply_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });

    register_simple_tac(get_tactic_eassumption_name(),
                        []() { return eassumption_tactic(); });
}

void finalize_apply_tactic() {
    delete g_apply_class_instance;
}
}
