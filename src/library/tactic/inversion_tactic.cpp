/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/error_msgs.h"
#include "library/io_state_stream.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/class_instance_synth.h"
#include "library/tactic/inversion_tactic.h"
#include "library/tactic/clear_tactic.h"

namespace lean {
namespace inversion {
result::result(list<goal> const & gs, list<list<expr>> const & args, list<implementation_list> const & imps,
               list<rename_map> const & rs, name_generator const & ngen, substitution const & subst):
    m_goals(gs), m_args(args), m_implementation_lists(imps),
    m_renames(rs), m_ngen(ngen), m_subst(subst) {
    lean_assert_eq(length(m_goals), length(m_args));
    lean_assert_eq(length(m_goals), length(m_implementation_lists));
    lean_assert_eq(length(m_goals), length(m_renames));
}
}

/**
    \brief Given eq_rec of the form <tt>@eq.rec.{l₂ l₁} A a (λ (a' : A) (h : a = a'), B a') b a p</tt>,
    apply the eq_rec_eq definition to produce the equality

       b = @eq.rec.{l₂ l₁} A a (λ (a' : A) (h : a = a'), B a') b a p

    The eq_rec_eq definition is of the form

    definition eq_rec_eq.{l₁ l₂} {A : Type.{l₁}} {B : A → Type.{l₂}} [h : is_hset A] {a : A} (b : B a) (p : a = a) :
       b = @eq.rec.{l₂ l₁} A a (λ (a' : A) (h : a = a'), B a') b a p :=
    ...
*/
optional<expr> apply_eq_rec_eq(type_checker & tc, io_state const & ios, list<expr> const & ctx, expr const & eq_rec) {
    buffer<expr> args;
    expr const & eq_rec_fn = get_app_args(eq_rec, args);
    if (args.size() != 6)
        return none_expr();
    expr const & p = args[5];
    if (!is_local(p) || !is_eq_a_a(tc, mlocal_type(p)))
        return none_expr();
    expr const & A = args[0];
    auto is_hset_A = mk_hset_instance(tc, ios, ctx, A);
    if (!is_hset_A)
        return none_expr();
    levels ls = const_levels(eq_rec_fn);
    level l2  = head(ls);
    level l1  = head(tail(ls));
    expr C    = tc.whnf(args[2]).first;
    if (!is_lambda(C))
        return none_expr();
    expr a1   = mk_local(tc.mk_fresh_name(), binding_domain(C));
    C         = tc.whnf(instantiate(binding_body(C), a1)).first;
    if (!is_lambda(C))
        return none_expr();
    C         = binding_body(C);
    if (!closed(C))
        return none_expr();
    expr B    = Fun(a1, C);
    expr a    = args[1];
    expr b    = args[3];
    expr r    = mk_constant(get_eq_rec_eq_name(), {l1, l2});
    return some_expr(mk_app({r, A, B, *is_hset_A, a, b, p}));
}

typedef inversion::implementation_ptr  implementation_ptr;
typedef inversion::implementation_list implementation_list;

static void replace(implementation_list const & imps, unsigned sz, expr const * from, expr const * to) {
    lean_assert(std::all_of(from, from+sz, is_local));
    for (implementation_ptr const & imp : imps) {
        imp->update_exprs([&](expr const & e) {
                return instantiate_rev(abstract_locals(e, sz, from), sz, to);
            });
    }
}

static void replace(implementation_list const & imps, buffer<expr> const & from, buffer<expr> const & to) {
    lean_assert(from.size() == to.size());
    return replace(imps, from.size(), from.data(), to.data());
}

static void replace(implementation_list const & imps, expr const & from, expr const & to) {
    return replace(imps, 1, &from, &to);
}

class inversion_tac {
    environment const &           m_env;
    io_state const &              m_ios;
    type_checker &                m_tc;
    list<name>                    m_ids;
    name_generator                m_ngen;
    substitution                  m_subst;

    bool                          m_dep_elim;
    bool                          m_proof_irrel;
    unsigned                      m_nparams;
    unsigned                      m_nindices;
    unsigned                      m_nminors;
    declaration                   m_I_decl;
    declaration                   m_cases_on_decl;

    bool                          m_throw_tactic_exception; // if true, then throw tactic_exception in case of failure, instead of returning none

    expr whnf(expr const & e) { return m_tc.whnf(e).first; }
    expr infer_type(expr const & e) { return m_tc.infer(e).first; }

    void init_inductive_info(name const & n) {
        m_dep_elim       = inductive::has_dep_elim(m_env, n);
        m_nindices       = *inductive::get_num_indices(m_env, n);
        m_nparams        = *inductive::get_num_params(m_env, n);
        // This tactic is bases on cases_on construction which only has
        // minor premises for the introduction rules of this datatype.
        // For non-mutually recursive datatypes inductive::get_num_intro_rules == inductive::get_num_minor_premises
        m_nminors        = *inductive::get_num_intro_rules(m_env, n);
        m_I_decl         = m_env.get(n);
        m_cases_on_decl  = m_env.get({n, "cases_on"});
    }

    bool is_inversion_applicable(expr const & t) {
        buffer<expr> args;
        expr const & fn = get_app_args(t, args);
        if (!is_constant(fn))
            return false;
        if (!inductive::is_inductive_decl(m_env, const_name(fn)))
            return false;
        if (!m_env.find(name{const_name(fn), "cases_on"}) || !m_env.find(get_eq_name()))
            return false;
        if (m_proof_irrel && !m_env.find(get_heq_name()))
            return false;
        init_inductive_info(const_name(fn));
        if (args.size() != m_nindices + m_nparams)
            return false;
        return true;
    }

    pair<expr, expr> mk_eq(expr const & lhs, expr const & rhs) {
        expr lhs_type = infer_type(lhs);
        expr rhs_type = infer_type(rhs);
        level l       = sort_level(m_tc.ensure_type(lhs_type).first);
        constraint_seq cs;
        if (m_tc.is_def_eq(lhs_type, rhs_type, justification(), cs) && !cs) {
            return mk_pair(mk_app(mk_constant(get_eq_name(), to_list(l)), lhs_type, lhs, rhs),
                           mk_app(mk_constant(get_eq_refl_name(), to_list(l)), rhs_type, rhs));
        } else {
            return mk_pair(mk_app(mk_constant(get_heq_name(), to_list(l)), lhs_type, lhs, rhs_type, rhs),
                           mk_app(mk_constant(get_heq_refl_name(), to_list(l)), rhs_type, rhs));
        }
    }

    void assign(goal const & g, expr const & val) {
        ::lean::assign(m_subst, g, val);
    }

    /** \brief We say h has independent indices IF
        1- it is *not* an indexed inductive family, OR
        2- it is an indexed inductive family, but all indices are distinct local constants,
        and all hypotheses of g different from h and indices, do not depend on the indices.
        3- if not m_dep_elim, then the conclusion does not depend on the indices.
    */
    bool has_indep_indices(goal const & g, expr const & h, expr const & h_type) {
        if (m_nindices == 0)
            return true;
        buffer<expr> args;
        get_app_args(h_type, args);
        lean_assert(m_nindices <= args.size());
        unsigned fidx = args.size() - m_nindices;
        for (unsigned i = fidx; i < args.size(); i++) {
            if (!is_local(args[i]))
                return false; // the indices must be local constants
            for (unsigned j = fidx; j < i; j++) {
                if (mlocal_name(args[j]) == mlocal_name(args[i]))
                    return false; // the indices must be distinct local constants
            }
        }
        if (!m_dep_elim) {
            expr const & g_type = g.get_type();
            if (std::any_of(args.end() - m_nindices, args.end(), [&](expr const & arg) { return depends_on(g_type, arg); }))
                return false;
        }
        buffer<expr> hyps;
        g.get_hyps(hyps);
        for (expr const & h1 : hyps) {
            if (mlocal_name(h1) == mlocal_name(h))
                continue;
            if (std::any_of(args.end() - m_nindices, args.end(),
                            [&](expr const & arg) { return mlocal_name(arg) == mlocal_name(h1); }))
                continue;
            // h1 is not h nor any of the indices
            // Thus, it must not depend on the indices
            if (std::any_of(args.end() - m_nindices, args.end(), [&](expr const & arg) { return depends_on(h1, arg); }))
                return false;
        }
        return true;
    }

    /** \brief Split hyps into two "telescopes".
        - non_deps : hypotheses that do not depend on H
        - deps     : hypotheses that depend on H (directly or indirectly)
    */
    void split_deps(buffer<expr> const & hyps, expr const & H, buffer<expr> & non_deps, buffer<expr> & deps) {
        for (expr const & hyp : hyps) {
            expr const & hyp_type = mlocal_type(hyp);
            if (depends_on(hyp_type, H) || std::any_of(deps.begin(), deps.end(), [&](expr const & dep) { return depends_on(hyp_type, dep); })) {
                deps.push_back(hyp);
            } else {
                non_deps.push_back(hyp);
            }
        }
    }

    /** \brief Given a goal of the form

              Ctx, h : I A j, D |- T

        where the type of h is the inductive datatype (I A j) where A are parameters,
        and j the indices. Generate the goal

              Ctx, h : I A j, D, j' : J, h' : I A j' |- j == j' -> h == h' -> T

        Remark: (j == j' -> h == h') is a "telescopic" equality. If the environment
        is proof irrelevant, it is built using homogenous and heterogeneous equalities.
        If the environment is proof relevant, it is built using homogeneous equality
        and the eq.rec (this construction is much more complex than the proof irrelevant
        one).

        Remark: j is sequence of terms, and j' a sequence of local constants.

        The original goal is solved if we can solve the produced goal.

        \remark h_type is mlocal_type(h) after normalization
    */
    goal generalize_indices(goal const & g, expr const & h, expr const & h_type) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr m            = g.get_meta();
        expr m_type       = g.get_type();
        name h_new_name   = get_unused_name(local_pp_name(h), hyps);
        buffer<expr> I_args;
        expr const & I    = get_app_args(h_type, I_args);
        expr h_new_type  = mk_app(I, I_args.size() - m_nindices, I_args.data());
        expr d           = whnf(infer_type(h_new_type));
        name t_prefix("t");
        unsigned nidx = 1;
        if (m_proof_irrel) {
            unsigned eq_idx  = 1;
            name eq_prefix("H");
            buffer<expr> ts;
            buffer<expr> eqs;
            buffer<expr> refls;
            auto add_eq = [&](expr const & lhs, expr const & rhs) {
                pair<expr, expr> p = mk_eq(lhs, rhs);
                expr new_eq   = p.first;
                expr new_refl = p.second;
                eqs.push_back(mk_local(m_ngen.next(), g.get_unused_name(eq_prefix, eq_idx), new_eq, binder_info()));
                refls.push_back(new_refl);
            };
            for (unsigned i = I_args.size() - m_nindices; i < I_args.size(); i++) {
                expr t_type = binding_domain(d);
                expr t      = mk_local(m_ngen.next(), g.get_unused_name(t_prefix, nidx), t_type, binder_info());
                expr const & index = I_args[i];
                add_eq(t, index);
                h_new_type  = mk_app(h_new_type, t);
                hyps.push_back(t);
                ts.push_back(t);
                d           = instantiate(binding_body(d), t);
            }
            expr h_new    = mk_local(m_ngen.next(), h_new_name, h_new_type, local_info(h));
            if (m_dep_elim)
                add_eq(h_new, h);
            hyps.push_back(h_new);
            expr new_type = Pi(eqs, g.get_type());
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            expr val      = mk_app(mk_app(mk_app(Fun(ts, Fun(h_new, new_meta)), m_nindices, I_args.end() - m_nindices), h),
                                   refls);
            assign(g, val);
            return new_g;
        } else {
            // proof relevant version
            buffer<expr> ss;
            buffer<expr> ts;
            buffer<expr> refls;
            for (unsigned i = I_args.size() - m_nindices; i < I_args.size(); i++) {
                expr t_type = binding_domain(d);
                expr t      = mk_local(m_ngen.next(), g.get_unused_name(t_prefix, nidx), t_type, binder_info());
                h_new_type  = mk_app(h_new_type, t);
                ss.push_back(I_args[i]);
                refls.push_back(mk_refl(m_tc, I_args[i]));
                hyps.push_back(t);
                ts.push_back(t);
                d           = instantiate(binding_body(d), t);
            }
            expr h_new    = mk_local(m_ngen.next(), h_new_name, h_new_type, local_info(h));
            ts.push_back(h_new);
            ss.push_back(h);
            refls.push_back(mk_refl(m_tc, h));
            hyps.push_back(h_new);
            buffer<expr> eqs;
            mk_telescopic_eq(m_tc, ss, ts, eqs);
            ts.pop_back();
            expr new_type = Pi(eqs, g.get_type());
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            expr val      = mk_app(mk_app(mk_app(Fun(ts, Fun(h_new, new_meta)), m_nindices, I_args.end() - m_nindices), h),
                                   refls);
            assign(g, val);
            return new_g;
        }
    }

    /** \brief Generalize h dependencies.

        This tactic uses this method only if has_indep_indices(hyps, h, h_type) returns true.

        The hypotheses that depend on h are stored in deps.
    */
    goal generalize_dependecies(goal const & g, expr const & h, buffer<expr> & deps) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        hyps.erase_elem(h);
        buffer<expr> non_deps;
        split_deps(hyps, h, non_deps, deps);
        buffer<expr> & new_hyps = non_deps;
        new_hyps.push_back(h);
        expr new_type = Pi(deps, g.get_type());
        expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, new_type)), new_hyps);
        goal new_g(new_meta, new_type);
        expr val      = mk_app(new_meta, deps);
        assign(g, val);
        return new_g;
    }

    /**
       \brief Given a goal of the form

                 Ctx, h : I A j |- T[h]

        produce the subgoals

                 Ctx, h : I A j |- b_1 : B_1 -> T [C_1 A b_1]
                 ...
                 Ctx, h : I A j |- b_n : B_n -> T [C_n A b_n]

        where the C_i's are the constructors (aka introduction rules) of the inductive datatype h.

        The hypothesis h must be the last hypothesis in the input goal. Consequently, no other
        hypothesis depends on it.

        The implementation list is external auxiliary data associated with constructors.
        For example, we use it to compile recursive equations. Each implementation corresponds to one
        equation. Each equation is tagged with a constructor C_i. The constructor is retrieved using
        the virtual method get_constructor_name. We split the list imps in n lists. One for each
        subgoal. An implementation associated with the constructor i is in the i-th resulting list.

        \remark This method assumes the indices j are local constants, and only h and j may depend on j.
    */
    std::pair<list<goal>, list<implementation_list>> apply_cases_on(goal const & g, implementation_list const & imps, bool has_indep_indices) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr const & h      = hyps.back();
        expr const & h_type = whnf(mlocal_type(h));
        buffer<expr> I_args;
        expr const & I      = get_app_args(h_type, I_args);
        name const & I_name = const_name(I);
        expr g_type         = g.get_type();
        expr cases_on;
        if (m_cases_on_decl.get_num_univ_params() != m_I_decl.get_num_univ_params()) {
            level g_lvl  = sort_level(m_tc.ensure_type(g_type).first);
            cases_on     = mk_constant({I_name, "cases_on"}, cons(g_lvl, const_levels(I)));
        } else {
            cases_on     = mk_constant({I_name, "cases_on"}, const_levels(I));
        }
        // add params
        cases_on          = mk_app(cases_on, m_nparams, I_args.data());
        // add type former
        expr type_former  = g_type;
        if (m_dep_elim)
            type_former   = Fun(h, type_former);
        type_former       = Fun(m_nindices, I_args.end() - m_nindices, type_former);
        cases_on          = mk_app(cases_on, type_former);
        // add indices
        cases_on          = mk_app(cases_on, m_nindices, I_args.end() - m_nindices);
        // add h
        cases_on          = mk_app(cases_on, h);
        buffer<name> intro_names;
        get_intro_rule_names(m_env, I_name, intro_names);
        lean_assert(m_nminors == intro_names.size());
        buffer<expr> new_hyps;
        if (has_indep_indices)
            new_hyps.append(hyps.size() - 1, hyps.data());
        else
            new_hyps.append(hyps.size() - m_nindices - 1, hyps.data());

        // add a subgoal for each minor premise of cases_on
        expr cases_on_type = whnf(infer_type(cases_on));
        buffer<goal> new_goals;
        buffer<implementation_list> new_imps;
        for (unsigned i = 0; i < m_nminors; i++) {
            expr new_type = binding_domain(cases_on_type);
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, new_type)), new_hyps);
            goal new_g(new_meta, new_type);
            new_goals.push_back(new_g);
            cases_on      = mk_app(cases_on, new_meta);
            cases_on_type = whnf(binding_body(cases_on_type)); // the minor premises do not depend on each other
            name const & intro_name = intro_names[i];
            new_imps.push_back(filter(imps, [&](implementation_ptr const & imp) { return imp->get_constructor_name() == intro_name; }));
        }
        assign(g, cases_on);
        return mk_pair(to_list(new_goals), to_list(new_imps));
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

    /**
       The method apply_cases_on produces subgoals of the form

                 Ctx, h : I A j |- b_i : B_i -> T [C_i A b_i]

       The b_i are the arguments of the constructor C_i.
       This method moves the b_i's to the hypotheses list.
    */
    std::pair<list<goal>, list<list<expr>>> intros_minors_args(list<goal> gs) {
        buffer<unsigned> minors_nargs;
        get_minors_nargs(minors_nargs);
        lean_assert(length(gs) == minors_nargs.size());
        buffer<goal> new_gs;
        buffer<list<expr>> new_args;
        for (unsigned i = 0; i < minors_nargs.size(); i++) {
            goal const & g = head(gs);
            unsigned nargs = minors_nargs[i];
            buffer<expr> hyps;
            g.get_hyps(hyps);
            buffer<expr> new_hyps;
            new_hyps.append(hyps);
            expr g_type    = g.get_type();
            buffer<expr> curr_new_args;
            for (unsigned i = 0; i < nargs; i++) {
                expr type  = binding_domain(g_type);
                name new_h_name;
                if (m_ids) {
                    new_h_name = head(m_ids);
                    m_ids      = tail(m_ids);
                } else {
                    new_h_name = binding_name(g_type);
                }
                expr new_h = mk_local(m_ngen.next(), get_unused_name(new_h_name, new_hyps), type, binder_info());
                curr_new_args.push_back(new_h);
                new_hyps.push_back(new_h);
                g_type     = instantiate(binding_body(g_type), new_h);
            }
            new_args.push_back(to_list(curr_new_args));
            g_type = head_beta_reduce(g_type);
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, g_type)), new_hyps);
            goal new_g(new_meta, g_type);
            new_gs.push_back(new_g);
            expr val      = Fun(nargs, new_hyps.end() - nargs, new_meta);
            assign(g, val);
            gs = tail(gs);
        }
        return mk_pair(to_list(new_gs), to_list(new_args));
    }

    // auxiliary exception used to interrupt execution
    struct inversion_exception {};

    [[ noreturn ]] void throw_ill_formed_goal() {
        if (m_throw_tactic_exception)
            throw tactic_exception("invalid 'cases' tactic, ill-formed goal");
        else
            throw inversion_exception();
    }

    [[ noreturn ]] void throw_ill_typed_goal() {
        if (m_throw_tactic_exception)
            throw tactic_exception("invalid 'cases' tactic, ill-typed goal");
        else
            throw inversion_exception();
    }

    void throw_lift_down_failure() {
        if (m_throw_tactic_exception)
            throw tactic_exception("invalid 'cases' tactic, lift.down failed");
        else
            throw inversion_exception();
    }

    void throw_unification_eq_rec_failure(goal const & g, expr const & eq) {
        if (m_throw_tactic_exception) {
            throw tactic_exception([=](formatter const & fmt) {
                    format r("invalid 'cases' tactic, unification failed to eliminate eq.rec in the homogeneous equality");
                    r += pp_indent_expr(fmt, eq);
                    r += compose(line(), format("auxiliary goal at time of failure"));
                    r += nest(get_pp_indent(fmt.get_options()), compose(line(), g.pp(fmt)));
                    return r;
                });
        } else {
            throw inversion_exception();
        }
    }

    /** \brief Process goal of the form:  Pi (H : eq.rec A s C a s p = b), R
        The idea is to reduce it to
            Pi (H : a = b), R
        when A is a hset
        and then invoke intro_next_eq recursively.

        \remark \c type is the type of \c g after some normalization
    */
    goal intro_next_eq_rec(goal const & g, expr const & type) {
        lean_assert(is_pi(type));
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr const & eq  = binding_domain(type);
        expr const & lhs = app_arg(app_fn(eq));
        expr const & rhs = app_arg(eq);
        lean_assert(is_eq_rec(lhs));
        // lhs is of the form  (eq.rec A s C a s p)
        // aux_eq is a term of type ((eq.rec A s C a s p) = a)
        auto aux_eq = apply_eq_rec_eq(m_tc, m_ios, to_list(hyps), lhs);
        if (!aux_eq || has_expr_metavar_relaxed(*aux_eq)) {
            throw_unification_eq_rec_failure(g, eq);
        }
        buffer<expr> lhs_args;
        get_app_args(lhs, lhs_args);
        expr const & reduced_lhs = lhs_args[3];
        expr new_eq      = ::lean::mk_eq(m_tc, reduced_lhs, rhs);
        expr new_type    = update_binding(type, new_eq, binding_body(type));
        expr new_meta    = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
        goal new_g(new_meta, new_type);
        // create assignment for g
        expr A           = infer_type(lhs);
        level lvl        = sort_level(m_tc.ensure_type(A).first);
        // old_eq : eq.rec A s C a s p = b
        expr old_eq      = mk_local(m_ngen.next(), binding_name(type), eq, binder_info());
        // aux_eq : a = eq.rec A s C a s p
        expr trans_eq    = mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, reduced_lhs, lhs, rhs, *aux_eq, old_eq});
        // trans_eq : a = b
        expr val         = Fun(old_eq, mk_app(new_meta, trans_eq));
        assign(g, val);
        return intro_next_eq(new_g);
    }

    /**
       \brief Process goal of the form:  Ctx |- Pi (H : a == b), R   when a and b have the same type
       The idea is to reduce it to
           Ctx, H : a = b |- R
       This method is only used if the environment has a proof irrelevant Prop.
    */
    goal intro_next_heq(goal const & g) {
        lean_assert(m_proof_irrel);
        expr const & type   = g.get_type();
        expr eq             = binding_domain(type);
        lean_assert(const_name(get_app_fn(eq)) == get_heq_name());
        buffer<expr> args;
        expr const & heq_fn = get_app_args(eq, args);
        constraint_seq cs;
        if (m_tc.is_def_eq(args[0], args[2], justification(), cs) && !cs) {
            buffer<expr> hyps;
            g.get_hyps(hyps);
            expr new_eq   = mk_app(mk_constant(get_eq_name(), const_levels(heq_fn)), args[0], args[1], args[3]);
            expr new_hyp  = mk_local(m_ngen.next(), g.get_unused_name(binding_name(type)), new_eq, binder_info());
            expr new_type = instantiate(binding_body(type), new_hyp);
            hyps.push_back(new_hyp);
            expr new_mvar = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
            expr new_meta = mk_app(new_mvar, hyps);
            goal new_g(new_meta, new_type);
            hyps.pop_back();
            expr H        = mk_local(m_ngen.next(), g.get_unused_name(binding_name(type)), binding_domain(type), binder_info());
            expr to_eq    = mk_app(mk_constant(get_heq_to_eq_name(), const_levels(heq_fn)), args[0], args[1], args[3], H);
            expr val      = Fun(H, mk_app(mk_app(new_mvar, hyps), to_eq));
            assign(g, val);
            return new_g;
        } else {
            if (m_throw_tactic_exception) {
                throw tactic_exception("invalid 'cases' tactic, unification failed to reduce heterogeneous equality into homogeneous one");
            } else {
                throw inversion_exception();
            }
        }
    }

    /** \brief Process goal of the form:  Ctx |- Pi (H : a = b), R
        The idea is to reduce it to
            Ctx, H : a = b |- R

         \remark \c type is the type of \c g after some normalization
    */
    goal intro_next_eq_simple(goal const & g, expr const & type) {
        expr eq            = binding_domain(type);
        lean_assert(const_name(get_app_fn(eq)) == get_eq_name());
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr new_hyp  = mk_local(m_ngen.next(), g.get_unused_name(binding_name(type)), binding_domain(type), binder_info());
        expr new_type = instantiate(binding_body(type), new_hyp);
        hyps.push_back(new_hyp);
        expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
        goal new_g(new_meta, new_type);
        expr val      = Fun(new_hyp, new_meta);
        assign(g, val);
        return new_g;
    }

    goal intro_next_eq(goal const & g) {
        expr type          = g.get_type();
        if (!is_pi(type))
            throw_ill_formed_goal();
        expr eq            = binding_domain(type);
        expr const & eq_fn = get_app_fn(eq);
        if (!is_constant(eq_fn))
            throw_ill_formed_goal();
        if (const_name(eq_fn) == get_eq_name()) {
            expr const & lhs = app_arg(app_fn(eq));
            expr const & rhs = app_arg(eq);
            expr new_lhs     = whnf(lhs);
            expr new_rhs     = whnf(rhs);
            if (lhs != new_lhs || rhs != new_rhs) {
                eq   = mk_app(app_fn(app_fn(eq)), new_lhs, new_rhs);
                type = update_binding(type, eq, binding_body(type));
            }
            if (!m_proof_irrel && is_eq_rec(new_lhs)) {
                return intro_next_eq_rec(g, type);
            } else {
                return intro_next_eq_simple(g, type);
            }
        } else if (m_proof_irrel && const_name(eq_fn) == get_heq_name()) {
            return intro_next_heq(g);
        } else {
            throw_ill_formed_goal();
        }
    }

    /**
       \brief The no_confusion constructions uses lifts in the proof relevant version.
       We must apply lift.down to eliminate the auxiliary lift.
    */
    expr lift_down(expr const & v) {
        if (!m_proof_irrel) {
            expr v_type       = whnf(infer_type(v));
            if (!is_app(v_type)) {
                throw_lift_down_failure();
            }
            expr const & lift = app_fn(v_type);
            if (!is_constant(lift) || const_name(lift) != get_lift_name()) {
                throw_lift_down_failure();
            }
            return mk_app(mk_constant(get_lift_down_name(), const_levels(lift)), app_arg(v_type), v);
        } else {
            return v;
        }
    }

    buffer<expr>        m_c_args; // current intro/constructor args that may be renamed by unify_eqs
    rename_map          m_renames;
    implementation_list m_imps;

    void store_rename(expr const & old_hyp, expr const & new_hyp) {
        for (expr & c_arg : m_c_args) {
            if (is_local(c_arg) && mlocal_name(old_hyp) == mlocal_name(c_arg))
                c_arg = new_hyp;
        }
        if (is_local(new_hyp))
            m_renames.insert(mlocal_name(old_hyp), mlocal_name(new_hyp));
    }

    /** \brief Update m_renames with old_hyps --> new_hyps. */
    void store_renames(buffer<expr> const & old_hyps, buffer<expr> const & new_hyps) {
        lean_assert(old_hyps.size() == new_hyps.size());
        for (unsigned i = 0; i < old_hyps.size(); i++) {
            store_rename(old_hyps[i], new_hyps[i]);
        }
    }

    // Remark: it also updates m_renames and m_imps
    optional<goal> unify_eqs(goal g, unsigned neqs) {
        if (neqs == 0)
            return optional<goal>(g); // done
        g = intro_next_eq(g);
        buffer<expr> hyps;
        g.get_hyps(hyps);
        lean_assert(!hyps.empty());
        expr Heq = hyps.back();
        buffer<expr> Heq_args;
        get_app_args(mlocal_type(Heq), Heq_args);
        expr const & A   = whnf(Heq_args[0]);
        expr lhs         = whnf(Heq_args[1]);
        expr rhs         = whnf(Heq_args[2]);
        constraint_seq cs;
        if (m_proof_irrel && m_tc.is_def_eq(lhs, rhs, justification(), cs) && !cs) {
            // deletion transition: t == t
            hyps.pop_back(); // remove t == t equality
            expr new_type = g.get_type();
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            assign(g, new_meta);
            return unify_eqs(new_g, neqs-1);
        }
        buffer<expr> lhs_args, rhs_args;
        expr const & lhs_fn = get_app_args(lhs, lhs_args);
        expr const & rhs_fn = get_app_args(rhs, rhs_args);
        expr const & g_type = g.get_type();
        level const & g_lvl = sort_level(m_tc.ensure_type(g_type).first);
        if (is_constant(lhs_fn) &&
            is_constant(rhs_fn) &&
            inductive::is_intro_rule(m_env, const_name(lhs_fn)) &&
            inductive::is_intro_rule(m_env, const_name(rhs_fn))) {
            buffer<expr> A_args;
            expr const & A_fn   = get_app_args(A, A_args);
            if (!is_constant(A_fn) || !inductive::is_inductive_decl(m_env, const_name(A_fn)))
                throw_ill_typed_goal();
            name no_confusion_name(const_name(A_fn), "no_confusion");
            if (!m_env.find(no_confusion_name)) {
                if (m_throw_tactic_exception)
                    throw tactic_exception(sstream() << "invalid 'cases' tactic, construction '" << no_confusion_name << "' is not available in the environment");
                else
                    throw inversion_exception();
            }
            expr no_confusion = mk_app(mk_app(mk_constant(no_confusion_name, cons(g_lvl, const_levels(A_fn))), A_args), g_type, lhs, rhs, Heq);
            if (const_name(lhs_fn) == const_name(rhs_fn)) {
                // injectivity transition
                expr new_type = binding_domain(whnf(infer_type(no_confusion)));
                if (m_proof_irrel || !depends_on(g_type, hyps.back()))
                    hyps.pop_back(); // remove processed equality
                expr new_mvar = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
                expr new_meta = mk_app(new_mvar, hyps);
                goal new_g(new_meta, new_type);
                expr val      = lift_down(mk_app(no_confusion, new_meta));
                assign(g, val);
                unsigned A_nparams = *inductive::get_num_params(m_env, const_name(A_fn));
                lean_assert(lhs_args.size() >= A_nparams);
                return unify_eqs(new_g, neqs - 1 + lhs_args.size() - A_nparams);
            } else {
                // conflict transition, Heq is of the form c_1 ... = c_2 ..., where c_1 and c_2 are different constructors/intro rules.
                expr val      = lift_down(no_confusion);
                assign(g, val);
                return optional<goal>(); // goal has been solved
            }
        }
        if (is_local(rhs)) {
            // solution transition, Heq is of the form t = y, where y is a local constant

            // assume the current goal is of the form
            //
            //  non_deps, deps[rhs], H : lhs = rhs |- C[rhs]
            //
            //  We use non_deps to denote hypotheses that do not depend on rhs,
            //  and deps[rhs] to denote hypotheses that depend on it.
            //
            //  The resultant goal is of the form
            //
            //  non_deps, deps[lhs] |- C[lhs]
            //
            // Now, assume ?m1 is a solution for the resultant goal.
            // Then,
            //
            //     @eq.rec A lhs (fun rhs, Pi(deps[rhs], C[rhs])) (?m1 non_deps) rhs H deps[rhs]
            //
            // is a solution for the original goal.
            // Remark: A is the type of lhs and rhs
            hyps.pop_back(); // remove processed equality
            buffer<expr> non_deps, deps;
            split_deps(hyps, rhs, non_deps, deps);
            if (deps.empty() && !depends_on(g_type, rhs)) {
                // eq.rec is not necessary
                buffer<expr> & new_hyps = non_deps;
                expr new_type           = g_type;
                expr new_mvar           = mk_metavar(m_ngen.next(), Pi(new_hyps, new_type));
                expr new_meta           = mk_app(new_mvar, new_hyps);
                goal new_g(new_meta, new_type);
                assign(g, new_meta);
                return unify_eqs(new_g, neqs-1);
            } else {
                expr deps_g_type    = Pi(deps, g_type);
                level eq_rec_lvl1   = sort_level(m_tc.ensure_type(deps_g_type).first);
                level eq_rec_lvl2   = sort_level(m_tc.ensure_type(A).first);
                expr tformer;
                if (m_proof_irrel)
                    tformer = Fun(rhs, deps_g_type);
                else
                    tformer = Fun(rhs, Fun(Heq, deps_g_type));
                expr eq_rec         = mk_constant(get_eq_rec_name(), {eq_rec_lvl1, eq_rec_lvl2});
                eq_rec              = mk_app(eq_rec, A, lhs, tformer);
                buffer<expr> new_hyps;
                new_hyps.append(non_deps);
                expr new_type       = instantiate(abstract_local(deps_g_type, rhs), lhs);
                store_rename(rhs, lhs);
                replace(m_imps, rhs, lhs);
                if (!m_proof_irrel) {
                    new_type = abstract_local(new_type, Heq);
                    new_type = instantiate(new_type, mk_refl(m_tc, lhs));
                }
                buffer<expr> new_deps;
                for (unsigned i = 0; i < deps.size(); i++) {
                    expr new_hyp = mk_local(m_ngen.next(), binding_name(new_type), binding_domain(new_type),
                                            binding_info(new_type));
                    new_hyps.push_back(new_hyp);
                    new_deps.push_back(new_hyp);
                    new_type     = instantiate(binding_body(new_type), new_hyp);
                }
                replace(m_imps, deps, new_deps);
                lean_assert(deps.size() == new_deps.size());
                store_renames(deps, new_deps);
                expr new_mvar       = mk_metavar(m_ngen.next(), Pi(new_hyps, new_type));
                expr new_meta       = mk_app(new_mvar, new_hyps);
                goal new_g(new_meta, new_type);
                expr eq_rec_minor   = mk_app(new_mvar, non_deps);
                eq_rec              = mk_app(eq_rec, eq_rec_minor, rhs, Heq);
                expr val            = mk_app(eq_rec, deps);
                assign(g, val);
                return unify_eqs(new_g, neqs-1);
            }
        } else if (is_local(lhs)) {
            // flip equation and reduce to previous case
            expr symm_eq   = mk_eq(rhs, lhs).first;
            hyps.pop_back(); // remove processed equality
            if (!depends_on(g_type, Heq)) {
                expr new_type  = mk_arrow(symm_eq, g_type);
                expr new_mvar  = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
                expr new_meta  = mk_app(new_mvar, hyps);
                goal new_g(new_meta, new_type);
                expr Heq_inv   = mk_symm(m_tc, Heq);
                expr val       = mk_app(new_meta, Heq_inv);
                assign(g, val);
                return unify_eqs(new_g, neqs);
            } else {
                // Let C[Heq] be the original conclusion which depends on the equality eq being processed.
                expr new_Heq     = update_mlocal(Heq, symm_eq);
                expr new_Heq_inv = mk_symm(m_tc, new_Heq);
                expr new_type    = Pi(new_Heq, instantiate(abstract_local(g_type, Heq), new_Heq_inv));
                expr new_mvar    = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
                expr new_meta    = mk_app(new_mvar, hyps);
                goal new_g(new_meta, new_type);
                // Then, we have
                // new_meta : Pi (new_Heq : rhs = lhs), C[symm new_Heq]
                expr Heq_inv   = mk_symm(m_tc, Heq);
                expr val       = mk_app(new_meta, Heq_inv);
                // val      : C[symm (symm Heq)]
                // Remark: in proof irrelevant mode (symm (symm Heq)) is definitionally equal to Heq
                if (!m_proof_irrel) {
                    expr C      = Fun(Heq, g_type);
                    level A_lvl = sort_level(m_tc.ensure_type(A).first);
                    level g_lvl = sort_level(m_tc.ensure_type(g_type).first);
                    expr elim_inv_inv = mk_constant(get_eq_elim_inv_inv_name(), {A_lvl, g_lvl});
                    val         = mk_app({elim_inv_inv, A, lhs, rhs, C, Heq, val});
                    // val : C[Heq] as we wanted
                }
                assign(g, val);
                return unify_eqs(new_g, neqs);
            }
        }
        if (m_throw_tactic_exception) {
            throw tactic_exception([=](formatter const & fmt) {
                    format r("invalid 'cases' tactic, unification failed");
                    r += compose(line(), format("auxiliary goal at time of failure"));
                    r += nest(get_pp_indent(fmt.get_options()), compose(line(), g.pp(fmt)));
                    return r;
                });
        } else {
            throw inversion_exception();
        }
    }

    auto unify_eqs(list<goal> const & gs, list<list<expr>> args, list<implementation_list> imps) ->
        std::tuple<list<goal>, list<list<expr>>, list<implementation_list>, list<rename_map>> {
        lean_assert(length(gs) == length(imps));
        unsigned neqs = m_nindices + (m_dep_elim ? 1 : 0);
        buffer<goal>                new_goals;
        buffer<list<expr>>          new_args;
        buffer<implementation_list> new_imps;
        buffer<rename_map>          new_renames;
        for (goal const & g : gs) {
            flet<rename_map>          set1(m_renames, rename_map());
            flet<implementation_list> set2(m_imps,    head(imps));
            m_c_args.clear();
            to_buffer(head(args), m_c_args);
            if (optional<goal> new_g = unify_eqs(g, neqs)) {
                new_goals.push_back(*new_g);
                list<expr> new_as = to_list(m_c_args);
                new_args.push_back(new_as);
                new_imps.push_back(m_imps);
                new_renames.push_back(m_renames);
            }
            imps  = tail(imps);
            args = tail(args);
        }
        return std::make_tuple(to_list(new_goals), to_list(new_args), to_list(new_imps), to_list(new_renames));
    }

    std::pair<goal, rename_map> intro_deps(goal const & g, buffer<expr> const & deps) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        buffer<expr> new_hyps;
        new_hyps.append(hyps);
        rename_map rs;
        expr g_type    = g.get_type();
        for (expr const & d : deps) {
            expr type  = binding_domain(g_type);
            expr new_d = mk_local(m_ngen.next(), get_unused_name(local_pp_name(d), new_hyps), type, local_info(d));
            rs.insert(mlocal_name(d), mlocal_name(new_d));
            new_hyps.push_back(new_d);
            g_type     = instantiate(binding_body(g_type), new_d);
        }
        expr new_meta  = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, g_type)), new_hyps);
        goal new_g(new_meta, g_type);
        unsigned ndeps = deps.size();
        expr val       = Fun(ndeps, new_hyps.end() - ndeps, new_meta);
        assign(g, val);
        return mk_pair(new_g, rs);
    }

    std::pair<list<goal>, list<rename_map>> intro_deps(list<goal> const & gs, buffer<expr> const & deps) {
        buffer<goal> new_goals;
        buffer<rename_map> new_rs;
        for (goal const & g : gs) {
            auto p = intro_deps(g, deps);
            new_goals.push_back(p.first);
            new_rs.push_back(p.second);
        }
        return mk_pair(to_list(new_goals), to_list(new_rs));
    }

    goal clear_hypothesis(goal const & g, name const & h) {
        if (auto p = g.find_hyp_from_internal_name(h)) {
            expr const & h = p->first;
            unsigned i     = p->second;
            buffer<expr> hyps;
            g.get_hyps(hyps);
            hyps.erase(hyps.size() - i - 1);
            if (depends_on(g.get_type(), h) || depends_on(i, hyps.end() - i, h)) {
                return g; // other hypotheses or result type depend on h
            }
            expr new_type = g.get_type();
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            assign(g, new_meta);
            return new_g;
        } else {
            return g;
        }
    }

    // Remove hypothesis of the form (H : a = a)
    goal remove_eq_refl_hypotheses(goal g) {
        buffer<name> to_remove;
        buffer<expr> hyps;
        g.get_hyps(hyps);
        for (expr const & h : hyps) {
            expr const & h_type = mlocal_type(h);
            if (!is_eq(h_type))
                continue;
            expr const & lhs = app_arg(app_fn(h_type));
            expr const & rhs = app_arg(h_type);
            if (lhs == rhs)
                to_remove.push_back(mlocal_name(h));
        }
        for (name const & h : to_remove) {
            g = clear_hypothesis(g, h);
        }
        return g;
    }

    list<goal> clear_hypothesis(list<goal> const & gs, list<rename_map> rs, name const & h_name, expr const & h_type) {
        buffer<goal> new_gs;
        optional<name> lhs_name; // If h_type is of the form lhs = rhs, and lhs is also a hypothesis, then we also remove it.
        if (is_eq(h_type) && is_local(app_arg(app_fn(h_type)))) {
            lhs_name = mlocal_name(app_arg(app_fn(h_type)));
        }
        for (goal const & g : gs) {
            rename_map const & m = head(rs);
            goal new_g = clear_hypothesis(g, m.find(h_name));
            if (lhs_name)
                new_g = clear_hypothesis(new_g, *lhs_name);
            if (!m_proof_irrel)
                new_g = remove_eq_refl_hypotheses(new_g);
            new_gs.push_back(new_g);
            rs = tail(rs);
        }
        return to_list(new_gs);
    }

public:
    inversion_tac(environment const & env, io_state const & ios, name_generator const & ngen,
                  type_checker & tc, substitution const & subst, list<name> const & ids,
                  bool throw_tactic_ex):
        m_env(env), m_ios(ios), m_tc(tc), m_ids(ids),
        m_ngen(ngen), m_subst(subst), m_throw_tactic_exception(throw_tactic_ex) {
        m_proof_irrel = m_env.prop_proof_irrel();
    }

    inversion_tac(environment const & env, io_state const & ios, type_checker & tc):
        inversion_tac(env, ios, tc.mk_ngen(), tc, substitution(), list<name>(), false) {}

    typedef inversion::result result;

    optional<result> execute(goal const & g, expr const & h, implementation_list const & imps) {
        try {
            expr h_type                         = whnf(mlocal_type(h));
            if (!is_inversion_applicable(h_type))
                return optional<result>();
            if (has_indep_indices(g, h, h_type)) {
                buffer<expr> deps;
                goal g1                             = generalize_dependecies(g, h, deps);
                auto gs_imps_pair                   = apply_cases_on(g1, imps, true);
                list<goal> gs2                      = gs_imps_pair.first;
                list<implementation_list> new_imps  = gs_imps_pair.second;
                auto gs_args_pair                   = intros_minors_args(gs2);
                list<goal> gs3                      = gs_args_pair.first;
                list<list<expr>> args               = gs_args_pair.second;
                auto gs_rs_pair                     = intro_deps(gs3, deps);
                list<goal> gs4                      = gs_rs_pair.first;
                list<rename_map> rs                 = gs_rs_pair.second;
                return optional<result>(result(gs4, args, new_imps, rs, m_ngen, m_subst));
            } else {
                goal g1                             = generalize_indices(g, h, h_type);
                auto gs_imps_pair                   = apply_cases_on(g1, imps, false);
                list<goal> gs2                      = gs_imps_pair.first;
                list<implementation_list> new_imps  = gs_imps_pair.second;
                auto gs_args_pair                   = intros_minors_args(gs2);
                list<goal> gs3                      = gs_args_pair.first;
                list<list<expr>> args               = gs_args_pair.second;
                list<goal> gs4;
                list<rename_map> rs;
                std::tie(gs4, args, new_imps, rs)   = unify_eqs(gs3, args, new_imps);
                gs4 = clear_hypothesis(gs4, rs, mlocal_name(h), h_type);
                return optional<result>(result(gs4, args, new_imps, rs, m_ngen, m_subst));
            }
        } catch (inversion_exception & ex) {
            return optional<result>();
        }
    }

    optional<result> execute(goal const & g, name const & n, implementation_list const & imps) {
        auto p         = g.find_hyp(n);
        if (!p) {
            if (m_throw_tactic_exception)
                throw tactic_exception(sstream() << "invalid 'cases' tactic, unknown hypothesis '" << n << "'");
            return optional<result>();
        }
        expr const & h = p->first;
        return execute(g, h, imps);
    }
};

namespace inversion {
optional<result> apply(environment const & env, io_state const & ios, type_checker & tc,
                       goal const & g, expr const & h, implementation_list const & imps) {
    return inversion_tac(env, ios, tc).execute(g, h, imps);
}
}

tactic inversion_tactic(name const & n, list<name> const & ids) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & ps) -> optional<proof_state> {
        goals const & gs  = ps.get_goals();
        if (empty(gs))
            return none_proof_state();
        goal  g           = head(gs);
        goals tail_gs     = tail(gs);
        name_generator ngen              = ps.get_ngen();
        std::unique_ptr<type_checker> tc = mk_type_checker(env, ngen.mk_child(), ps.relax_main_opaque());
        inversion_tac tac(env, ios, ngen, *tc, ps.get_subst(), ids, ps.report_failure());
        if (auto res = tac.execute(g, n, implementation_list())) {
            proof_state new_s(ps, append(res->m_goals, tail_gs), res->m_subst, res->m_ngen);
            return some_proof_state(new_s);
        } else {
            return none_proof_state();
        }
    };
    return tactic01(fn);
}

void initialize_inversion_tactic() {
    register_tac(get_tactic_cases_name(),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name n = tactic_expr_to_id(app_arg(app_fn(e)), "invalid 'cases' tactic, argument must be an identifier");
                     buffer<name> ids;
                     get_tactic_id_list_elements(app_arg(e), ids, "invalid 'cases' tactic, list of identifiers expected");
                     return inversion_tactic(n, to_list(ids.begin(), ids.end()));
                 });
}
void finalize_inversion_tactic() {}
}
