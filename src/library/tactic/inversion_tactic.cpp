/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"
#include "library/tactic/tactic.h"
#include "library/reducible.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
class inversion_tac {
    environment const &           m_env;
    io_state const &              m_ios;
    proof_state const &           m_ps;
    name_generator                m_ngen;
    substitution                  m_subst;
    std::unique_ptr<type_checker> m_tc;

    unsigned                      m_nparams;
    unsigned                      m_nindices;
    unsigned                      m_nminors;
    declaration                   m_I_decl;
    declaration                   m_cases_on_decl;

    void init_inductive_info(name const & n) {
        m_nindices      = *inductive::get_num_indices(m_env, n);
        m_nparams       = *inductive::get_num_params(m_env, n);
        m_nminors       = *inductive::get_num_minor_premises(m_env, n);
        m_I_decl        = m_env.get(n);
        m_cases_on_decl = m_env.get({n, "cases_on"});
    }

    bool is_inversion_applicable(expr const & t) {
        buffer<expr> args;
        expr const & fn = get_app_args(t, args);
        if (!is_constant(fn))
            return false;
        if (!inductive::is_inductive_decl(m_env, const_name(fn)))
            return false;
        if (!m_env.find(name{const_name(fn), "cases_on"}) ||
            !m_env.find(name("eq")) || !m_env.find(name("heq")))
            return false;
        init_inductive_info(const_name(fn));
        if (args.size() != m_nindices + m_nparams)
            return false;
        return true;
    }

    pair<expr, expr> mk_eq(expr const & lhs, expr const & rhs) {
        expr lhs_type = m_tc->infer(lhs).first;
        expr rhs_type = m_tc->infer(rhs).first;
        level l       = sort_level(m_tc->ensure_type(lhs_type).first);
        constraint_seq cs;
        if (m_tc->is_def_eq(lhs_type, rhs_type, justification(), cs) && !cs) {
            return mk_pair(mk_app(mk_constant("eq", to_list(l)), lhs_type, lhs, rhs),
                           mk_app(mk_constant({"eq", "refl"}, to_list(l)), rhs_type, rhs));
        } else {
            return mk_pair(mk_app(mk_constant("heq", to_list(l)), lhs_type, lhs, rhs_type, rhs),
                           mk_app(mk_constant({"heq", "refl"}, to_list(l)), rhs_type, rhs));
        }
    }

    goal generalize_indices(goal const & g, expr const & h, expr const & h_type) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr m            = g.get_meta();
        expr m_type       = g.get_type();
        name h_new_name   = g.get_unused_name(local_pp_name(h));
        buffer<expr> I_args;
        expr const & I    = get_app_args(h_type, I_args);
        if (m_nindices > 0) {
            expr h_new_type  = mk_app(I, I_args.size() - m_nindices, I_args.data());
            expr d           = m_tc->whnf(m_tc->infer(h_new_type).first).first;
            unsigned eq_idx  = 1;
            name eq_prefix("H");
            buffer<expr> ts;
            buffer<expr> eqs;
            buffer<expr> refls;
            name t_prefix("t");
            unsigned nidx = 1;
            for (unsigned i = I_args.size() - m_nindices; i < I_args.size(); i++) {
                expr t_type = binding_domain(d);
                expr t      = mk_local(m_ngen.next(), g.get_unused_name(t_prefix, nidx), t_type, binder_info());
                expr const & index = I_args[i];
                pair<expr, expr> p = mk_eq(t, index);
                expr new_eq   = p.first;
                expr new_refl = p.second;
                eqs.push_back(mk_local(m_ngen.next(), g.get_unused_name(eq_prefix, eq_idx), new_eq, binder_info()));
                refls.push_back(new_refl);
                h_new_type  = mk_app(h_new_type, t);
                hyps.push_back(t);
                ts.push_back(t);
                d           = instantiate(binding_body(d), t);
            }
            expr h_new    = mk_local(m_ngen.next(), h_new_name, h_new_type, local_info(h));
            hyps.push_back(h_new);
            expr new_type = Pi(eqs, g.get_type());
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            expr val      = g.abstract(mk_app(mk_app(mk_app(Fun(ts, Fun(h_new, new_meta)), m_nindices, I_args.end() - m_nindices), h), refls));
            m_subst.assign(g.get_name(), val);
            return new_g;
        } else {
            expr h_new    = mk_local(m_ngen.next(), h_new_name, h_type, local_info(h));
            hyps.push_back(h_new);
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, g.get_type())), hyps);
            goal new_g(new_meta, g.get_type());
            expr val      = g.abstract(mk_app(new_meta, h));
            m_subst.assign(g.get_name(), val);
            return new_g;
        }
    }

    list<goal> apply_cases_on(goal const & g) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr const & h      = hyps.back();
        expr const & h_type = mlocal_type(h);
        buffer<expr> I_args;
        expr const & I      = get_app_args(h_type, I_args);
        expr g_type         = g.get_type();
        expr cases_on;
        if (length(m_cases_on_decl.get_univ_params()) != length(m_I_decl.get_univ_params())) {
            level g_lvl  = sort_level(m_tc->ensure_type(g_type).first);
            cases_on     = mk_constant({const_name(I), "cases_on"}, cons(g_lvl, const_levels(I)));
        } else {
            cases_on     = mk_constant({const_name(I), "cases_on"}, const_levels(I));
        }
        // add params
        cases_on          = mk_app(cases_on, m_nparams, I_args.data());
        // add type former
        expr type_former  = Fun(m_nindices, I_args.end() - m_nindices, g_type);
        cases_on          = mk_app(cases_on, type_former);
        // add indices
        cases_on          = mk_app(cases_on, m_nindices, I_args.end() - m_nindices);
        // add h
        cases_on          = mk_app(cases_on, h);
        buffer<expr> new_hyps;
        new_hyps.append(hyps.size() - m_nindices - 1, hyps.data());
        // add a subgoal for each minor premise of cases_on
        expr cases_on_type = m_tc->whnf(m_tc->infer(cases_on).first).first;
        buffer<goal> new_goals;
        for (unsigned i = 0; i < m_nminors; i++) {
            expr new_type = binding_domain(cases_on_type);
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, new_type)), new_hyps);
            goal new_g(new_meta, new_type);
            new_goals.push_back(new_g);
            cases_on      = mk_app(cases_on, new_meta);
            cases_on_type = m_tc->whnf(binding_body(cases_on_type)).first; // the minor premises do not depend on each other
        }
        expr val        = g.abstract(cases_on);
        m_subst.assign(g.get_name(), val);
        return to_list(new_goals.begin(), new_goals.end());
    }

    // Store in \c r the number of arguments for each cases_on minor.
    void get_minors_nargs(buffer<unsigned> & r) {
        expr cases_on_type = m_cases_on_decl.get_type();
        for (unsigned i = 0; i < m_nparams + 1 + m_nindices + 1; i++)
            cases_on_type = binding_body(cases_on_type);
        for (unsigned i = 0; i < m_nminors; i++) {
            expr minor_type = binding_domain(cases_on_type);
            unsigned nargs  = 0;
            while (is_pi(minor_type)) {
                nargs++;
                minor_type = binding_body(minor_type);
            }
            r.push_back(nargs);
            cases_on_type   = binding_body(cases_on_type);
        }
    }

    list<goal> intros_minors_args(list<goal> gs) {
        buffer<unsigned> minors_nargs;
        get_minors_nargs(minors_nargs);
        lean_assert(length(gs) == minors_nargs.size());
        buffer<goal> new_gs;
        for (unsigned i = 0; i < minors_nargs.size(); i++) {
            goal const & g = head(gs);
            unsigned nargs = minors_nargs[i];
            buffer<expr> hyps;
            g.get_hyps(hyps);
            buffer<expr> new_hyps;
            new_hyps.append(hyps);
            expr g_type    = g.get_type();
            for (unsigned i = 0; i < nargs; i++) {
                expr type  = binding_domain(g_type);
                expr new_h = mk_local(m_ngen.next(), get_unused_name(binding_name(g_type), hyps), type, binder_info());
                new_hyps.push_back(new_h);
                g_type     = instantiate(binding_body(g_type), new_h);
            }
            g_type = head_beta_reduce(g_type);
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, g_type)), new_hyps);
            goal new_g(new_meta, g_type);
            new_gs.push_back(new_g);
            expr val      = g.abstract(Fun(nargs, new_hyps.end() - nargs, new_meta));
            m_subst.assign(g.get_name(), val);
            gs = tail(gs);
        }
        return to_list(new_gs.begin(), new_gs.end());
    }

public:
    inversion_tac(environment const & env, io_state const & ios, proof_state const & ps):
        m_env(env), m_ios(ios), m_ps(ps),
        m_ngen(m_ps.get_ngen()),
        m_tc(mk_type_checker(m_env, m_ngen.mk_child(), m_ps.relax_main_opaque())) {
    }

    optional<proof_state> execute(name const & n) {
        goals const & gs  = m_ps.get_goals();
        if (empty(gs))
            return none_proof_state();
        goal  g           = head(gs);
        goals tail_gs     = tail(gs);
        auto p = g.find_hyp(n);
        if (!p)
            return none_proof_state();
        expr const & h    = p->first;
        expr h_type       = m_tc->whnf(mlocal_type(h)).first;
        if (!is_inversion_applicable(h_type))
            return none_proof_state();
        goal g1           = generalize_indices(g, h, h_type);
        list<goal> g2s    = apply_cases_on(g1);
        list<goal> g3s    = intros_minors_args(g2s);
        proof_state new_s(m_ps, append(g3s, tail_gs), m_subst, m_ngen);
        return some_proof_state(new_s);
    }
};

tactic inversion_tactic(name const & n) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & ps) -> optional<proof_state> {
        inversion_tac tac(env, ios, ps);
        return tac.execute(n);
    };
    return tactic01(fn);
}

void initialize_inversion_tactic() {
    register_tac(name({"tactic", "inversion"}),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name n = tactic_expr_to_id(app_arg(e), "invalid 'inversion' tactic, argument must be an identifier");
                     return inversion_tactic(n);
                 });
}
void finalize_inversion_tactic() {}
}
