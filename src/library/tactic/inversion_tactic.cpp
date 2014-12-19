/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/io_state_stream.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/class_instance_synth.h"

namespace lean {
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
    if (!is_local(p) || !is_eq_a_a(mlocal_type(p)))
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
    expr r    = mk_constant("eq_rec_eq", {l1, l2});
    return some_expr(mk_app({r, A, B, *is_hset_A, a, b, p}));
}

class inversion_tac {
    environment const &           m_env;
    io_state const &              m_ios;
    proof_state const &           m_ps;
    list<name>                    m_ids;
    name_generator                m_ngen;
    substitution                  m_subst;
    std::unique_ptr<type_checker> m_tc;

    bool                          m_dep_elim;
    bool                          m_proof_irrel;
    unsigned                      m_nparams;
    unsigned                      m_nindices;
    unsigned                      m_nminors;
    declaration                   m_I_decl;
    declaration                   m_cases_on_decl;


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
        if (!m_env.find(name{const_name(fn), "cases_on"}) || !m_env.find(name("eq")))
            return false;
        if (m_proof_irrel && !m_env.find(name("heq")))
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

    void assign(name const & n, expr const & val) {
        m_subst.assign(n, val);
    }

    goal generalize_indices(goal const & g, expr const & h, expr const & h_type) {
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr m            = g.get_meta();
        expr m_type       = g.get_type();
        name h_new_name   = get_unused_name(local_pp_name(h), hyps);
        buffer<expr> I_args;
        expr const & I    = get_app_args(h_type, I_args);
        expr h_new_type  = mk_app(I, I_args.size() - m_nindices, I_args.data());
        expr d           = m_tc->whnf(m_tc->infer(h_new_type).first).first;
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
            expr val      = g.abstract(mk_app(mk_app(mk_app(Fun(ts, Fun(h_new, new_meta)), m_nindices, I_args.end() - m_nindices), h),
                                              refls));
            assign(g.get_name(), val);
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
                refls.push_back(mk_refl(*m_tc, I_args[i]));
                hyps.push_back(t);
                ts.push_back(t);
                d           = instantiate(binding_body(d), t);
            }
            expr h_new    = mk_local(m_ngen.next(), h_new_name, h_new_type, local_info(h));
            ts.push_back(h_new);
            ss.push_back(h);
            refls.push_back(mk_refl(*m_tc, h));
            hyps.push_back(h_new);
            buffer<expr> eqs;
            mk_telescopic_eq(*m_tc, ss, ts, eqs);
            ts.pop_back();
            expr new_type = Pi(eqs, g.get_type());
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            expr val      = g.abstract(mk_app(mk_app(mk_app(Fun(ts, Fun(h_new, new_meta)), m_nindices, I_args.end() - m_nindices), h),
                                              refls));
            assign(g.get_name(), val);
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
        expr type_former  = g_type;
        if (m_dep_elim)
            type_former   = Fun(h, type_former);
        type_former       = Fun(m_nindices, I_args.end() - m_nindices, type_former);
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
        assign(g.get_name(), val);
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
                name new_h_name;
                if (m_ids) {
                    new_h_name = head(m_ids);
                    m_ids      = tail(m_ids);
                } else {
                    new_h_name = binding_name(g_type);
                }
                expr new_h = mk_local(m_ngen.next(), get_unused_name(new_h_name, new_hyps), type, binder_info());
                new_hyps.push_back(new_h);
                g_type     = instantiate(binding_body(g_type), new_h);
            }
            g_type = head_beta_reduce(g_type);
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(new_hyps, g_type)), new_hyps);
            goal new_g(new_meta, g_type);
            new_gs.push_back(new_g);
            expr val      = g.abstract(Fun(nargs, new_hyps.end() - nargs, new_meta));
            assign(g.get_name(), val);
            gs = tail(gs);
        }
        return to_list(new_gs.begin(), new_gs.end());
    }

    struct inversion_exception : public exception {
        inversion_exception(char const * msg):exception(msg) {}
        inversion_exception(sstream const & strm):exception(strm) {}
    };

    [[ noreturn ]] void throw_ill_formed_goal() {
        throw inversion_exception("ill-formed goal");
    }

    [[ noreturn ]] void throw_ill_typed_goal() {
        throw inversion_exception("ill-typed goal");
    }

    void throw_unification_eq_rec_failure() {
        throw inversion_exception("unification failed to eliminate eq.rec in homogeneous equality");
    }

    // Process goal of the form:  Pi (H : eq.rec A s C a s p = b), R
    // The idea is to reduce it to
    //        Pi (H : a = b), R
    // when A is a hset
    // and then invoke intro_next_eq recursively.
    //
    // \remark \c type is the type of \c g after whnf
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
        auto aux_eq = apply_eq_rec_eq(*m_tc, m_ios, to_list(hyps), lhs);
        if (!aux_eq)
            throw_unification_eq_rec_failure();
        buffer<expr> lhs_args;
        get_app_args(lhs, lhs_args);
        expr const & reduced_lhs = lhs_args[3];
        expr new_eq      = ::lean::mk_eq(*m_tc, reduced_lhs, rhs);
        expr new_type    = update_binding(type, new_eq, binding_body(type));
        expr new_meta    = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
        goal new_g(new_meta, new_type);
        // create assignment for g
        expr A           = m_tc->infer(lhs).first;
        level lvl        = sort_level(m_tc->ensure_type(A).first);
        // old_eq : eq.rec A s C a s p = b
        expr old_eq      = mk_local(m_ngen.next(), binding_name(type), eq, binder_info());
        // aux_eq : a = eq.rec A s C a s p
        expr trans_eq    = mk_app({mk_constant(name{"eq", "trans"}, {lvl}), A, reduced_lhs, lhs, rhs, *aux_eq, old_eq});
        // trans_eq : a = b
        expr val         = g.abstract(Fun(old_eq, mk_app(new_meta, trans_eq)));
        assign(g.get_name(), val);
        return intro_next_eq(new_g);
    }

    // Process goal of the form:  Ctx |- Pi (H : a == b), R   when a and b have the same type
    // The idea is to reduce it to
    //        Ctx, H : a = b |- R
    // This method is only used if the environment has a proof irrelevant Prop.
    //
    // \remark \c type is the type of \c g after whnf
    goal intro_next_heq(goal const & g, expr const & type) {
        lean_assert(m_proof_irrel);
        expr eq             = binding_domain(type);
        lean_assert(const_name(get_app_fn(eq)) == "heq");
        buffer<expr> args;
        expr const & heq_fn = get_app_args(eq, args);
        constraint_seq cs;
        if (m_tc->is_def_eq(args[0], args[2], justification(), cs) && !cs) {
            buffer<expr> hyps;
            g.get_hyps(hyps);
            expr new_eq   = mk_app(mk_constant("eq", const_levels(heq_fn)), args[0], args[1], args[3]);
            expr new_hyp  = mk_local(m_ngen.next(), g.get_unused_name(binding_name(type)), new_eq, binder_info());
            expr new_type = instantiate(binding_body(type), new_hyp);
            hyps.push_back(new_hyp);
            expr new_mvar = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
            expr new_meta = mk_app(new_mvar, hyps);
            goal new_g(new_meta, new_type);
            hyps.pop_back();
            expr H        = mk_local(m_ngen.next(), g.get_unused_name(binding_name(type)), binding_domain(type), binder_info());
            expr to_eq    = mk_app(mk_constant({"heq", "to_eq"}, const_levels(heq_fn)), args[0], args[1], args[3], H);
            expr val      = g.abstract(Fun(H, mk_app(mk_app(new_mvar, hyps), to_eq)));
            assign(g.get_name(), val);
            return new_g;
        } else {
            throw inversion_exception("unification failed to reduce heterogeneous equality into homogeneous one");
        }
    }

    // Process goal of the form:  Ctx |- Pi (H : a = b), R
    // The idea is to reduce it to
    //        Ctx, H : a = b |- R
    //
    // \remark \c type is the type of \c g after whnf
    goal intro_next_eq_simple(goal const & g, expr const & type) {
        expr eq            = binding_domain(type);
        lean_assert(const_name(get_app_fn(eq)) == "eq");
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr new_hyp  = mk_local(m_ngen.next(), g.get_unused_name(binding_name(type)), binding_domain(type), binder_info());
        expr new_type = instantiate(binding_body(type), new_hyp);
        hyps.push_back(new_hyp);
        expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
        goal new_g(new_meta, new_type);
        expr val      = g.abstract(Fun(new_hyp, new_meta));
        assign(g.get_name(), val);
        return new_g;
    }

    goal intro_next_eq(goal const & g) {
        expr const & type  = m_tc->whnf(g.get_type()).first;
        if (!is_pi(type))
            throw_ill_formed_goal();
        expr eq            = binding_domain(type);
        expr const & eq_fn = get_app_fn(eq);
        if (!is_constant(eq_fn))
            throw_ill_formed_goal();
        if (const_name(eq_fn) == "eq") {
            expr const & lhs = app_arg(app_fn(eq));
            if (!m_proof_irrel && is_eq_rec(lhs)) {
                return intro_next_eq_rec(g, type);
            } else {
                return intro_next_eq_simple(g, type);
            }
        } else if (m_proof_irrel && const_name(eq_fn) == "heq") {
            return intro_next_heq(g, type);
        } else {
            throw_ill_formed_goal();
        }
    }

    // Split hyps into two "telescopes".
    //   - non_deps : hypotheses that do not depend on rhs
    //   - deps     : hypotheses that depend on rhs (directly or indirectly)
    void split_deps(buffer<expr> const & hyps, expr const & rhs, buffer<expr> & non_deps, buffer<expr> & deps) {
        for (expr const & hyp : hyps) {
            expr const & hyp_type = mlocal_type(hyp);
            if (depends_on(hyp_type, rhs) || std::any_of(deps.begin(), deps.end(), [&](expr const & dep) { return depends_on(hyp_type, dep); })) {
                deps.push_back(hyp);
            } else {
                non_deps.push_back(hyp);
            }
        }
    }

    // The no_confusion constructions uses lifts in the proof relevant version.
    // We must apply lift.down to eliminate the auxiliary lift.
    expr lift_down(expr const & v) {
        if (!m_proof_irrel) {
            expr v_type       = m_tc->whnf(m_tc->infer(v).first).first;
            if (!is_app(v_type))
                throw_unification_eq_rec_failure();
            expr const & lift = app_fn(v_type);
            if (!is_constant(lift) || const_name(lift) != "lift")
                throw_unification_eq_rec_failure();
            return mk_app(mk_constant(name{"lift", "down"}, const_levels(lift)), app_arg(v_type), v);
        } else {
            return v;
        }
    }

    optional<goal> unify_eqs(goal g, unsigned neqs) {
        if (neqs == 0)
            return optional<goal>(g); // done
        g = intro_next_eq(g);
        buffer<expr> hyps;
        g.get_hyps(hyps);
        lean_assert(!hyps.empty());
        expr eq = hyps.back();
        buffer<expr> eq_args;
        get_app_args(mlocal_type(eq), eq_args);
        expr const & A   = m_tc->whnf(eq_args[0]).first;
        expr lhs         = m_tc->whnf(eq_args[1]).first;
        expr rhs         = m_tc->whnf(eq_args[2]).first;
        constraint_seq cs;
        if (m_proof_irrel && m_tc->is_def_eq(lhs, rhs, justification(), cs) && !cs) {
            // deletion transition: t == t
            hyps.pop_back(); // remove t == t equality
            expr new_type = g.get_type();
            expr new_meta = mk_app(mk_metavar(m_ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            expr val      = g.abstract(new_meta);
            assign(g.get_name(), val);
            return unify_eqs(new_g, neqs-1);
        }
        buffer<expr> lhs_args, rhs_args;
        expr const & lhs_fn = get_app_args(lhs, lhs_args);
        expr const & rhs_fn = get_app_args(rhs, rhs_args);
        expr const & g_type = g.get_type();
        level const & g_lvl = sort_level(m_tc->ensure_type(g_type).first);
        if (is_constant(lhs_fn) &&
            is_constant(rhs_fn) &&
            inductive::is_intro_rule(m_env, const_name(lhs_fn)) &&
            inductive::is_intro_rule(m_env, const_name(rhs_fn))) {
            buffer<expr> A_args;
            expr const & A_fn   = get_app_args(A, A_args);
            if (!is_constant(A_fn) || !inductive::is_inductive_decl(m_env, const_name(A_fn)))
                throw_ill_typed_goal();
            name no_confusion_name(const_name(A_fn), "no_confusion");
            if (!m_env.find(no_confusion_name))
                throw inversion_exception(sstream() << "construction '" << no_confusion_name << "' is not available in the environment");
            expr no_confusion = mk_app(mk_app(mk_constant(no_confusion_name, cons(g_lvl, const_levels(A_fn))), A_args), g_type, lhs, rhs, eq);
            if (const_name(lhs_fn) == const_name(rhs_fn)) {
                // injectivity transition
                expr new_type = binding_domain(m_tc->whnf(m_tc->infer(no_confusion).first).first);
                if (m_proof_irrel)
                    hyps.pop_back(); // remove processed equality
                expr new_mvar = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
                expr new_meta = mk_app(new_mvar, hyps);
                goal new_g(new_meta, new_type);
                expr val      = g.abstract(lift_down(mk_app(no_confusion, new_meta)));
                assign(g.get_name(), val);
                unsigned A_nparams = *inductive::get_num_params(m_env, const_name(A_fn));
                lean_assert(lhs_args.size() >= A_nparams);
                return unify_eqs(new_g, neqs - 1 + lhs_args.size() - A_nparams);
            } else {
                // conflict transition, eq is of the form c_1 ... = c_2 ..., where c_1 and c_2 are different constructors/intro rules.
                expr val      = g.abstract(lift_down(no_confusion));
                assign(g.get_name(), val);
                return optional<goal>(); // goal has been solved
            }
        }
        if (is_local(rhs)) {
            // solution transition, eq is of the form t = y, where y is a local constant

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
            expr deps_g_type    = Pi(deps, g_type);
            level eq_rec_lvl1   = sort_level(m_tc->ensure_type(deps_g_type).first);
            level eq_rec_lvl2   = sort_level(m_tc->ensure_type(A).first);
            expr tformer;
            if (m_proof_irrel)
                tformer = Fun(rhs, deps_g_type);
            else
                tformer = Fun(rhs, Fun(eq, deps_g_type));
            expr eq_rec         = mk_constant(name{"eq", "rec"}, {eq_rec_lvl1, eq_rec_lvl2});
            eq_rec              = mk_app(eq_rec, A, lhs, tformer);
            buffer<expr> new_hyps;
            new_hyps.append(non_deps);
            expr new_type       = instantiate(abstract_local(deps_g_type, rhs), lhs);
            if (!m_proof_irrel) {
                new_type = abstract_local(new_type, eq);
                new_type = instantiate(new_type, mk_refl(*m_tc, lhs));
            }
            for (unsigned i = 0; i < deps.size(); i++) {
                expr new_hyp = mk_local(m_ngen.next(), binding_name(new_type), binding_domain(new_type),
                                        binding_info(new_type));
                new_hyps.push_back(new_hyp);
                new_type     = instantiate(binding_body(new_type), new_hyp);
            }
            expr new_mvar       = mk_metavar(m_ngen.next(), Pi(new_hyps, new_type));
            expr new_meta       = mk_app(new_mvar, new_hyps);
            goal new_g(new_meta, new_type);
            expr eq_rec_minor   = mk_app(new_mvar, non_deps);
            eq_rec              = mk_app(eq_rec, eq_rec_minor, rhs, eq);
            expr val            = g.abstract(mk_app(eq_rec, deps));
            assign(g.get_name(), val);
            return unify_eqs(new_g, neqs-1);
        } else if (is_local(lhs)) {
            // flip equation and reduce to previous case
            if (m_proof_irrel)
                hyps.pop_back(); // remove processed equality
            expr symm_eq   = mk_eq(rhs, lhs).first;
            expr new_type  = mk_arrow(symm_eq, g_type);
            expr new_mvar = mk_metavar(m_ngen.next(), Pi(hyps, new_type));
            expr new_meta = mk_app(new_mvar, hyps);
            goal new_g(new_meta, new_type);
            level eq_symm_lvl = sort_level(m_tc->ensure_type(A).first);
            expr symm_pr  = mk_constant(name{"eq", "symm"}, {eq_symm_lvl});
            symm_pr       = mk_app(symm_pr, A, lhs, rhs, eq);
            expr val      = g.abstract(mk_app(new_meta, symm_pr));
            assign(g.get_name(), val);
            return unify_eqs(new_g, neqs);
        }
        // unification failed
        return optional<goal>(g);
    }

    list<goal> unify_eqs(list<goal> const & gs) {
        unsigned neqs = m_nindices + (m_dep_elim ? 1 : 0);
        buffer<goal> new_goals;
        for (goal const & g : gs) {
            if (optional<goal> new_g = unify_eqs(g, neqs))
                new_goals.push_back(*new_g);
        }
        return to_list(new_goals.begin(), new_goals.end());
    }

public:
    inversion_tac(environment const & env, io_state const & ios, proof_state const & ps, list<name> const & ids):
        m_env(env), m_ios(ios), m_ps(ps), m_ids(ids),
        m_ngen(m_ps.get_ngen()), m_subst(m_ps.get_subst()),
        m_tc(mk_type_checker(m_env, m_ngen.mk_child(), m_ps.relax_main_opaque())) {
        m_proof_irrel = m_env.prop_proof_irrel();
    }

    optional<proof_state> execute(name const & n) {
        try {
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
            list<goal> gs2    = apply_cases_on(g1);
            list<goal> gs3    = intros_minors_args(gs2);
            list<goal> gs4    = unify_eqs(gs3);
            proof_state new_s(m_ps, append(gs4, tail_gs), m_subst, m_ngen);
            return some_proof_state(new_s);
        } catch (inversion_exception & ex) {
            return none_proof_state();
        }
    }
};

tactic inversion_tactic(name const & n, list<name> const & ids) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & ps) -> optional<proof_state> {
        inversion_tac tac(env, ios, ps, ids);
        return tac.execute(n);
    };
    return tactic01(fn);
}

void initialize_inversion_tactic() {
    register_tac(name({"tactic", "inversion"}),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name n = tactic_expr_to_id(app_arg(e), "invalid 'inversion/cases' tactic, argument must be an identifier");
                     return inversion_tactic(n, list<name>());
                 });
    register_tac(name({"tactic", "inversion_with"}),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name n = tactic_expr_to_id(app_arg(app_fn(e)), "invalid 'cases-with' tactic, argument must be an identifier");
                     buffer<name> ids;
                     get_tactic_id_list_elements(app_arg(e), ids, "invalid 'cases-with' tactic, list of identifiers expected");
                     return inversion_tactic(n, to_list(ids.begin(), ids.end()));
                 });
}
void finalize_inversion_tactic() {}
}
