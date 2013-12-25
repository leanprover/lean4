/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/replace_visitor.h"
#include "library/fo_unify.h"
#include "library/placeholder.h"
#include "library/kernel_bindings.h"
#include "library/elaborator/elaborator.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
#include "library/tactic/apply_tactic.h"

#include "kernel/formatter.h"

namespace lean {
static name g_tmp_mvar_name = name::mk_internal_unique_name();
// The proof is based on an application of a function that returns a proof.
// There are two kinds of arguments:
//    1) regular arguments computed using unification.
//    2) propositions that generate new subgoals.
typedef std::pair<name, hypotheses> proposition_arg;
// We use a pair to simulate this "union" type.
typedef list<std::pair<optional<expr>, optional<proposition_arg>>> arg_list;

/**
   \brief Return the proof builder for the apply_tactic.

   It solves the goal \c gname by applying \c th_fun to the arguments \c alist.
*/
proof_builder mk_apply_tac_proof_builder(proof_builder const & pb, name const & gname, expr const & th_fun, arg_list const & alist) {
    return mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
            proof_map new_m(m);
            buffer<expr> args;
            args.push_back(th_fun);
            for (auto const & p2 : alist) {
                optional<expr> const & arg = p2.first;
                if (arg) {
                    // TODO(Leo): decide if we instantiate the metavars in the end or not.
                    args.push_back(*arg);
                } else {
                    proposition_arg const & parg = *(p2.second);
                    name const & subgoal_name = parg.first;
                    expr pr = find(m, subgoal_name);
                    for (auto p : parg.second)
                        pr = Fun(p.first, p.second, pr);
                    args.push_back(pr);
                    new_m.erase(subgoal_name);
                }
            }
            std::reverse(args.begin() + 1, args.end());
            new_m.insert(gname, mk_app(args));
            return pb(new_m, a);
        });
}

/**
   \brief Functional object for replacing placeholders with
   metavariables and attaching type to constants that refer
   hypotheses in the given goal.
*/
class apply_tactic_preprocessor_fn : public replace_visitor {
    ro_environment const & m_env;
    metavar_env const &    m_menv;
    hypotheses const &     m_hypotheses;
protected:
    expr visit_constant(expr const & e, context const & c) {
        if (is_placeholder(e)) {
            return m_menv->mk_metavar(c, const_type(e));
        } else if (m_env->find_object(const_name(e))) {
            return e;
        } else {
            for (auto const & p : m_hypotheses) {
                if (p.first == const_name(e))
                    return mk_constant(const_name(e), p.second);
            }
            throw exception(sstream() << "apply_tactic failed, unknown identifier '" << const_name(e) << "'");
        }
    }

public:
    apply_tactic_preprocessor_fn(ro_environment const & env, metavar_env const & menv, hypotheses const & hs):
        m_env(env), m_menv(menv), m_hypotheses(hs) {}
};

/**
   \brief Functional object for moving the metavariable occurring in an expression to
   another metavar environment.
*/
class move_metavars_fn : public replace_visitor {
    name_map<expr>         m_map;
    metavar_env const &    m_menv;
    expr visit_metavar(expr const & mvar, context const &) {
        name const & mvar_name = metavar_name(mvar);
        auto it = m_map.find(mvar_name);
        if (it == m_map.end()) {
            expr r = m_menv->mk_metavar();
            m_map[mvar_name] = r;
            return r;
        } else {
            return it->second;
        }
    }
public:
    move_metavars_fn(metavar_env const & menv):m_menv(menv) {}
};

static optional<proof_state> apply_tactic(ro_environment const & env, proof_state const & s,
                                          expr th, optional<expr> const & th_type) {
    precision prec = s.get_precision();
    if ((prec != precision::Precise && prec != precision::Over) || empty(s.get_goals())) {
        // it is pointless to apply this tactic, since it will produce UnderOver
        return none_proof_state();
    }
    type_checker checker(env);
    auto const & p       = head(s.get_goals());
    name const & gname   = p.first;
    goal const & g       = p.second;
    metavar_env new_menv = s.get_menv().copy();
    expr th_type_c;
    if (th_type) {
        th_type_c = *th_type;
    } else {
        metavar_env tmp_menv;
        buffer<unification_constraint> ucs;
        th = apply_tactic_preprocessor_fn(env, tmp_menv, g.get_hypotheses())(th);
        th_type_c = checker.check(th, context(), tmp_menv, ucs);
        elaborator elb(env, tmp_menv, ucs.size(), ucs.data());
        try {
            metavar_env new_tmp_menv = elb.next();
            th        = new_tmp_menv->instantiate_metavars(th);
            th_type_c = new_tmp_menv->instantiate_metavars(th_type_c);
        } catch (exception & ex) {
            return none_proof_state();
        }
        move_metavars_fn move(new_menv);
        th        = move(th);
        th_type_c = move(th_type_c);
    }
    expr conclusion = th_type_c;
    buffer<expr> mvars;
    unsigned i = 0;
    while (is_pi(conclusion)) {
        expr mvar = new_menv->mk_metavar();
        mvars.push_back(mvar);
        conclusion = instantiate(abst_body(conclusion), mvar, new_menv);
        i++;
    }
    optional<substitution> subst = fo_unify(conclusion, g.get_conclusion());
    if (!subst) {
        return none_proof_state();
    }
    th_type_c = apply(*subst, th_type_c);
    th        = apply(*subst, th);
    arg_list alist;
    unsigned new_goal_idx = 1;
    buffer<std::pair<name, goal>> new_goals_buf;
    for (auto const & mvar : mvars) {
        expr mvar_subst = apply(*subst, mvar);
        if (mvar_subst != mvar) {
            alist = cons(mk_pair(some_expr(mvar_subst), optional<proposition_arg>()), alist);
            th_type_c = instantiate(abst_body(th_type_c), mvar_subst, new_menv);
        } else {
            expr arg_type = abst_domain(th_type_c);
            if (checker.is_flex_proposition(arg_type, context(), new_menv)) {
                name new_gname(gname, new_goal_idx);
                new_goal_idx++;
                hypotheses hs = g.get_hypotheses();
                update_hypotheses_fn add_hypothesis(hs);
                hypotheses extra_hs;
                while (is_pi(arg_type)) {
                    expr d = abst_domain(arg_type);
                    name n = arg_to_hypothesis_name(abst_name(arg_type), d, env, context(), new_menv);
                    n   = add_hypothesis(n, d);
                    extra_hs.emplace_front(n, d);
                    arg_type = instantiate(abst_body(arg_type), mk_constant(n, d), new_menv);
                }
                alist = cons(mk_pair(none_expr(), some(proposition_arg(new_gname, extra_hs))), alist);
                new_goals_buf.emplace_back(new_gname, goal(add_hypothesis.get_hypotheses(), arg_type));
                th_type_c = instantiate(abst_body(th_type_c), mk_constant(new_gname, arg_type), new_menv);
            } else {
                // we have to create a new metavar in menv
                // since we do not have a substitution for mvar, and
                // it is not a proposition
                /// expr new_m = new_menv->mk_metavar(context(), some_expr(arg_type));
                alist = cons(mk_pair(some_expr(mvar), optional<proposition_arg>()), alist);
                th_type_c = instantiate(abst_body(th_type_c), mvar, new_menv);
            }
        }
    }
    proof_builder pb = s.get_proof_builder();
    proof_builder new_pb = mk_apply_tac_proof_builder(pb, gname, th, alist);
    goals new_gs = to_list(new_goals_buf.begin(), new_goals_buf.end(), tail(s.get_goals()));
    return some(proof_state(precision::Over, new_gs, new_menv, new_pb, s.get_cex_builder()));
}

tactic apply_tactic(expr const & th) {
    return mk_tactic01([=](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            // th may contain placeholder
            // TODO(Leo)
            return apply_tactic(env, s, th, none_expr());
        });
}

tactic apply_tactic(expr const & th, expr const & th_type) {
    return mk_tactic01([=](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            return apply_tactic(env, s, th, some_expr(th_type));
        });
}

tactic apply_tactic(name const & th_name) {
    return mk_tactic01([=](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            optional<object> obj = env->find_object(th_name);
            if (obj && (obj->is_theorem() || obj->is_axiom()))
                return apply_tactic(env, s, mk_constant(th_name), some_expr(obj->get_type()));
            else
                return none_proof_state();
        });
}

int mk_apply_tactic(lua_State * L) {
    if (is_expr(L, 1))
        return push_tactic(L, apply_tactic(to_expr(L, 1)));
    else
        return push_tactic(L, apply_tactic(to_name_ext(L, 1)));
}

void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_apply_tactic,     "apply_tac");
}
}
