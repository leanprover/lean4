/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/inverse.h"
#include "library/trace.h"
#include "library/constructions/injective.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/tactic/cases_tactic.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/subst_tactic.h"

namespace lean {
struct cases_tactic_exception : public ext_exception {
    tactic_state m_s;
    std::function<format()> m_msg;

    cases_tactic_exception(tactic_state const & s, std::function<format()> const & msg) :
        m_s(s), m_msg(msg) {}

    virtual format pp(formatter const &) const override { return m_msg(); }
    virtual throwable * clone() const override { return new cases_tactic_exception(m_s, m_msg); }
    virtual void rethrow() const override { throw cases_tactic_exception(m_s, m_msg); }
};

struct cases_tactic_fn {
    environment const &           m_env;
    options const &               m_opts;
    transparency_mode             m_mode;
    metavar_context &             m_mctx;
    /* User provided ids to name new hypotheses */
    list<name> &                  m_ids;
    /* If m_unfold_ginductive is true, then we normalize major premise type using relaxed_whnf,
       and expose the basic kernel inductive datatype. This feature is used by the equation compiler.
       The `cases` tactic exposed to users hides how the generalized inductive datatype implementation. */
    bool                          m_unfold_ginductive;

    /* Inductive datatype information */
    unsigned                      m_nparams;
    unsigned                      m_nindices;
    unsigned                      m_nminors;
    declaration                   m_I_decl;
    declaration                   m_cases_on_decl;

    type_context_old mk_type_context_for(metavar_decl const & g) {
        return ::lean::mk_type_context_for(m_env, m_opts, m_mctx, g.get_context(), m_mode);
    }

    type_context_old mk_type_context_for(expr const & mvar) {
        return mk_type_context_for(m_mctx.get_metavar_decl(mvar));
    }

    [[ noreturn ]] void throw_ill_formed_datatype() {
        throw exception("tactic cases failed, unexpected inductive datatype type");
    }

    tactic_state mk_tactic_state(expr const & mvar) {
        return mk_tactic_state_for_metavar(m_env, m_opts, "cases", m_mctx, mvar);
    }

    /* throw exception that stores the intermediate state */
    [[ noreturn ]] void throw_exception(expr const & mvar, char const * msg) {
        throw cases_tactic_exception { mk_tactic_state(mvar), [=] { return format(msg); } };
    }

    #define lean_cases_trace(MVAR, CODE) lean_trace(name({"tactic", "cases"}), type_context_old TMP_CTX = mk_type_context_for(MVAR); scope_trace_env _scope1(m_env, TMP_CTX); CODE)

    void init_inductive_info(name const & n) {
        m_nindices       = get_ginductive_num_indices(m_env, n);
        m_nparams        = get_ginductive_num_params(m_env, n);
        // This tactic is bases on cases_on construction which only has
        // minor premises for the introduction rules of this datatype.
        m_nminors        = length(get_ginductive_intro_rules(m_env, n));
        m_I_decl         = m_env.get(n);
        m_cases_on_decl  = m_env.get(get_dep_cases_on(m_env, n));
    }

    expr whnf_inductive(type_context_old & ctx, expr const & e) {
        if (m_unfold_ginductive)
            return ctx.relaxed_whnf(e);
        else
            return ::lean::whnf_ginductive(ctx, e);
    }

    /* For debugging purposes, check whether all hypotheses in Hs are in the local context for mvar */
    bool check_hypotheses_in_context(expr const & mvar, list<optional<name>> const & Hs) {
        local_context lctx = m_mctx.get_metavar_decl(mvar).get_context();
        for (optional<name> const & H : Hs) {
            if (H && !lctx.find_local_decl(*H)) {
                lean_unreachable();
                return false;
            }
        }
        return true;
    }

    bool is_cases_applicable(expr const & mvar, expr const & H) {
        type_context_old ctx = mk_type_context_for(mvar);
        expr t = whnf_inductive(ctx, ctx.infer(H));
        buffer<expr> args;
        expr const & fn = get_app_args(t, args);
        if (!is_constant(fn))
            return false;
        if (!is_ginductive(m_env, const_name(fn)))
            return false;
        if (!m_env.find(name{const_name(fn), "cases_on"}) || !m_env.find(get_eq_name()))
            return false;
        if (!m_env.find(get_heq_name()))
            return false;
        init_inductive_info(const_name(fn));
        if (args.size() != m_nindices + m_nparams)
            return false;
        lean_cases_trace(mvar, tout() << "inductive type: " << const_name(fn) <<
                         ", num. params: " << m_nparams << ", num. indices: " << m_nindices << "\n";);
        return true;
    }

    /** \brief We say h has independent indices IF
        1- it is *not* an indexed inductive family, OR
        2- it is an indexed inductive family, but all indices are distinct local constants,
        and all hypotheses of g different from h and indices, do not depend on the indices. */
    bool has_indep_indices(metavar_decl const & g, expr const & h) {
        lean_assert(is_local(h));
        if (m_nindices == 0)
            return true;
        type_context_old ctx = mk_type_context_for(g);
        expr h_type      = whnf_inductive(ctx, ctx.infer(h));
        buffer<expr> args;
        get_app_args(h_type, args);
        lean_assert(m_nindices <= args.size());
        unsigned fidx = args.size() - m_nindices;
        for (unsigned i = fidx; i < args.size(); i++) {
            if (!is_local(args[i]))
                return false; // the indices must be local constants
            for (unsigned j = 0; j < i; j++) {
                if (is_local(args[j]) && mlocal_name(args[j]) == mlocal_name(args[i]))
                    return false; // the indices must be distinct local constants
            }
        }
        local_context lctx          = g.get_context();
        optional<local_decl> h_decl = lctx.find_local_decl(h);
        lean_assert(h_decl);
        bool ok = true;
        lctx.for_each_after(*h_decl, [&](local_decl const & h1) {
                if (!ok) return;
                /* h1 must not depend on the indices */
                if (depends_on(h1, m_mctx, m_nindices, args.end() - m_nindices))
                    ok = false;
            });
        return ok;
    }

    pair<expr, expr> mk_eq(type_context_old & ctx, expr const & lhs, expr const & rhs) {
        // make sure we don't assign regular metavars at is_def_eq
        type_context_old::tmp_mode_scope scope(ctx);
        expr lhs_type = ctx.infer(lhs);
        expr rhs_type = ctx.infer(rhs);
        level l       = get_level(ctx, lhs_type);
        if (ctx.is_def_eq(lhs_type, rhs_type)) {
            return mk_pair(mk_app(mk_constant(get_eq_name(), to_list(l)), lhs_type, lhs, rhs),
                           mk_app(mk_constant(get_eq_refl_name(), to_list(l)), lhs_type, lhs));
        } else {
            return mk_pair(mk_app(mk_constant(get_heq_name(), to_list(l)), lhs_type, lhs, rhs_type, rhs),
                           mk_app(mk_constant(get_heq_refl_name(), to_list(l)), lhs_type, lhs));
        }
    }

    /** \brief Given a goal of the form

              Ctx, h : I A j, D |- T

        where the type of h is the inductive datatype (I A j) where A are parameters,
        and j the indices. Generate the goal

              Ctx, h : I A j, D, j' : J, h' : I A j' |- j == j' -> h == h' -> T

        Remark: (j == j' -> h == h') is a "telescopic" equality.

        Remark: this procedure assumes we have a standard environment

        Remark: j is sequence of terms, and j' a sequence of local constants.

        The original goal is solved if we can solve the produced goal. */
    expr generalize_indices(expr const & mvar, expr const & h, buffer<name> & new_indices_H, unsigned & num_eqs) {
        metavar_decl g     = m_mctx.get_metavar_decl(mvar);
        type_context_old ctx   = mk_type_context_for(g);
        expr h_type        = whnf_inductive(ctx, ctx.infer(h));
        buffer<expr> I_args;
        expr const & I     = get_app_args(h_type, I_args);
        lean_assert(I_args.size() == m_nparams + m_nindices);
        expr h_new_type    = mk_app(I, I_args.size() - m_nindices, I_args.data());
        expr d             = ctx.infer(h_new_type);
        name t_prefix("t");
        unsigned nidx = 1;
        name eq_prefix("H");
        unsigned eq_idx  = 1;
        buffer<expr> ts; /* new j' indices */
        buffer<expr> eqs;
        buffer<expr> refls;
        /* auxiliary function for populating eqs and refls. */
        auto add_eq = [&](expr const & lhs, expr const & rhs) {
            pair<expr, expr> p = mk_eq(ctx, lhs, rhs);
            expr new_eq_type   = p.first;
            expr new_eq_refl   = p.second;
            name new_eq_name   = ctx.lctx().get_unused_name(eq_prefix, eq_idx);
            eqs.push_back(ctx.push_local(new_eq_name, new_eq_type));
            refls.push_back(new_eq_refl);
        };
        /* create new indices and eqs */
        for (unsigned i = I_args.size() - m_nindices; i < I_args.size(); i++) {
            d           = ctx.try_to_pi(d);
            if (!is_pi(d))
                throw_ill_formed_datatype();
            expr t_type = binding_domain(d);
            expr t      = ctx.push_local(ctx.lctx().get_unused_name(t_prefix, nidx), t_type);
            ts.push_back(t);
            d           = instantiate(binding_body(d), t);
            h_new_type  = mk_app(h_new_type, t);
            expr const & index = I_args[i];
            add_eq(index, t);
        }
        name h_new_name = mlocal_pp_name(h);
        expr h_new      = ctx.push_local(h_new_name, h_new_type);
        add_eq(h, h_new);
        /* aux_type is  Pi (j' : J) (h' : I A j'), j == j' -> h == h' -> T */
        expr aux_type   = ctx.mk_pi(ts, ctx.mk_pi(h_new, ctx.mk_pi(eqs, g.get_type())));
        expr aux_mvar   = ctx.mk_metavar_decl(g.get_context(), aux_type);
        /* assign mvar := aux_mvar indices h refls */
        ctx.assign(mvar, mk_app(mk_app(mk_app(aux_mvar, m_nindices, I_args.end() - m_nindices), h), refls));
        /* introduce indices j' and h' */
        m_mctx = ctx.mctx();
        bool use_unused_names = false;
        auto r = intron(m_env, m_opts, m_mctx, aux_mvar, m_nindices + 1, new_indices_H, use_unused_names);
        lean_assert(r);
        num_eqs = eqs.size();
        return *r;
    }

    format pp_goal(expr const & mvar) {
        return mk_tactic_state(mvar).pp_goal(mvar);
    }

    list<expr> elim_aux_indices(list<expr> const & goals, buffer<name> const & aux_indices_H, hsubstitution_list & slist) {
        lean_assert(!slist || length(goals) == length(slist));
        buffer<expr>           new_goals;
        buffer<hsubstitution>  new_slist;
        list<expr> it1           = goals;
        hsubstitution_list it2   = slist;
        while (it1 && it2) {
            expr mvar            = head(it1);
            hsubstitution subst  = head(it2);
            name_set removed;
            lean_assert(aux_indices_H.size() > 1);
            unsigned i = aux_indices_H.size() - 1; /* last element is the auxiliary major premise */
            while (i > 0) {
                --i;
                name idx_name = aux_indices_H[i];
                removed.insert(idx_name);
                if (auto ridx = subst.find(idx_name)) {
                    lean_assert(is_local(*ridx));
                    name new_name = mlocal_name(*ridx);
                    subst.erase(idx_name);
                    idx_name = new_name;
                }
                expr H_idx = m_mctx.get_local(mvar, idx_name);
                mvar = clear(m_mctx, mvar, H_idx);
            }
            hsubstitution new_subst;
            subst.for_each([&](name const & from, expr const & to) {
                    lean_assert(is_local(to));
                    if (!removed.contains(mlocal_name(to)))
                        new_subst.insert(from, to);
                });
            new_goals.push_back(mvar);
            new_slist.push_back(new_subst);
            it1 = tail(it1);
            it2 = tail(it2);
        }
        slist = to_list(new_slist);
        return to_list(new_goals);
    }

    optional<inverse_info> invertible(expr const & lhs, expr const & rhs) {
        expr const & lhs_fn = get_app_fn(lhs);
        if (!is_constant(lhs_fn))
            return optional<inverse_info>();
        optional<inverse_info> r = has_inverse(m_env, const_name(lhs_fn));
        if (!r)
            return r;
        unsigned lhs_num_args = get_app_num_args(lhs);
        if (r->m_arity != lhs_num_args ||
            get_app_fn(rhs) != lhs_fn ||
            get_app_num_args(rhs) != lhs_num_args)
            return optional<inverse_info>();
        return r;
    }

    /* Create (f ... x) with the given arity, where the other arguments are inferred using
       type inference */
    expr mk_inverse(type_context_old & ctx, inverse_info const & inv, expr const & x) {
        buffer<bool> mask;
        mask.resize(inv.m_arity - 1, false);
        mask.push_back(true);
        return mk_app(ctx, inv.m_inv, mask.size(), mask.data(), &x);
    }

    optional<expr> unify_eqs(expr const & input_H, expr mvar, unsigned num_eqs, bool updating,
                             list<expr> & new_intros, hsubstitution & subst) {
        if (num_eqs == 0) {
            lean_cases_trace(mvar,
                             tout() << "solved equalities\n" << pp_goal(mvar) << "\n";
                             tout() << "input hypothesis: " << input_H << "\n";);
            /* clear input hypothesis */
            try {
                mvar = clear(m_mctx, mvar, input_H);
            } catch (exception&) { /* ignore failure */ }
            return some_expr(mvar);
        }
        expr A, B, lhs, rhs;
        lean_cases_trace(mvar, tout() << "unifying equalities [" << num_eqs << "]\n" << pp_goal(mvar) << "\n";);
        metavar_decl g       = m_mctx.get_metavar_decl(mvar);
        local_context lctx   = g.get_context();
        /* Normalize next equation lhs and rhs if needed */
        expr target          = g.get_type();
        lean_assert(is_pi(target) && is_arrow(target));
        if (is_eq(binding_domain(target), lhs, rhs)) {
            type_context_old ctx     = mk_type_context_for(mvar);
            expr lhs_n = whnf_gintro_rule(ctx, lhs);
            expr rhs_n = whnf_gintro_rule(ctx, rhs);
            if (lhs != lhs_n || rhs != rhs_n) {
                expr new_eq     = ::lean::mk_eq(ctx, lhs_n, rhs_n);
                expr new_target = mk_arrow(new_eq, binding_body(target));
                expr new_mvar   = ctx.mk_metavar_decl(lctx, new_target);
                ctx.assign(mvar, new_mvar);
                m_mctx          = ctx.mctx();
                mvar            = new_mvar;
                lean_cases_trace(mvar, tout() << "normalize lhs/rhs:\n" << pp_goal(mvar) << "\n";);
            }
        }
        /* Introduce next equality */
        optional<expr> mvar1 = intron(m_env, m_opts, m_mctx, mvar, 1, false);
        if (!mvar1) throw_exception(mvar, "cases tactic failed, unexpected failure when introducing auxiliary equatilies");
        metavar_decl g1      = m_mctx.get_metavar_decl(*mvar1);
        local_decl H_decl    = g1.get_context().get_last_local_decl();
        expr H_type          = H_decl.get_type();
        expr H               = H_decl.mk_ref();
        type_context_old ctx     = mk_type_context_for(*mvar1);
        if (is_heq(H_type, A, lhs, B, rhs)) {
            if (!ctx.is_def_eq(A, B)) {
                throw_exception(mvar, "cases tactic failed, when processing auxiliary heterogeneous equality");
            }
            /* Create helper goal mvar2 :  ctx |- lhs = rhs -> type, and assign
               mvar1 := mvar2 (eq_of_heq H) */
            expr new_target = mk_arrow(::lean::mk_eq(ctx, lhs, rhs), g1.get_type());
            expr mvar2      = ctx.mk_metavar_decl(lctx, new_target);
            expr val        = mk_app(mvar2, mk_eq_of_heq(ctx, H));
            ctx.assign(*mvar1, val);
            lean_cases_trace(mvar, tout() << "converted heq => eq\n";);
            m_mctx = ctx.mctx();
            return unify_eqs(input_H, mvar2, num_eqs, updating, new_intros, subst);
        } else if (is_eq(H_type, A, lhs, rhs)) {
            if (ctx.is_def_eq(lhs, rhs)) {
                lean_cases_trace(mvar, tout() << "skip\n";);
                expr mvar2 = clear(m_mctx, *mvar1, H);
                return unify_eqs(input_H, mvar2, num_eqs - 1, updating, new_intros, subst);
            } else if (is_local(rhs) || is_local(lhs)) {
                lean_cases_trace(mvar, tout() << "substitute\n";);
                hsubstitution extra_subst;
                bool symm  =
                    (!is_local(lhs) && is_local(rhs))
                    ||
                    (is_local(lhs) && is_local(rhs) &&
                     ctx.lctx().get_local_decl(lhs).get_idx()
                     <
                     ctx.lctx().get_local_decl(rhs).get_idx());
                if (symm && depends_on(lhs, m_mctx, ctx.lctx(), rhs)) {
                    throw_exception(mvar, "cases tactic failed, when eliminating equality left-hand-side depends on right-hand-side");
                } else if (!symm && depends_on(rhs, m_mctx, ctx.lctx(), lhs)) {
                    throw_exception(mvar, "cases tactic failed, when eliminating equality right-hand-side depends on left-hand-side");
                }
                expr mvar2 = ::lean::subst(m_env, m_opts, m_mode, m_mctx, *mvar1, H, symm,
                                           updating ? &extra_subst : nullptr);
                new_intros = apply(new_intros, extra_subst);
                subst      = merge(apply(subst, extra_subst), extra_subst);
                return unify_eqs(input_H, mvar2, num_eqs - 1, updating, new_intros, subst);
            } else if (auto info = invertible(lhs, rhs)) {
                lean_cases_trace(mvar, tout() << "invertible\n";);
                /* This branch is mainly used for equalities of the form
                       pack x = pack y
                   where pack is an auxiliary declaration introduced by
                   the equation compiler.
                */
                try {
                    expr lhs_arg            = app_arg(lhs);
                    expr rhs_arg            = app_arg(rhs);
                    expr inv_lhs            = mk_inverse(ctx, *info, lhs);
                    expr inv_fn             = app_fn(inv_lhs);
                    expr inv_lhs_eq_inv_rhs = mk_congr_arg(ctx, inv_fn, H);
                    expr inv_lhs_eq_lhs_arg = mk_app(ctx, info->m_lemma, lhs_arg);
                    expr inv_rhs_eq_rhs_arg = mk_app(ctx, info->m_lemma, rhs_arg);
                    expr lhs_arg_eq_rhs_arg = mk_eq_trans(ctx,
                                                          mk_eq_trans(ctx, mk_eq_symm(ctx, inv_lhs_eq_lhs_arg),
                                                                      inv_lhs_eq_inv_rhs),
                                                          inv_rhs_eq_rhs_arg);
                    expr new_target         = mk_arrow(::lean::mk_eq(ctx, lhs_arg, rhs_arg), g1.get_type());
                    expr mvar2              = m_mctx.mk_metavar_decl(lctx, new_target);
                    expr val                = mk_app(mvar2, lhs_arg_eq_rhs_arg);
                    m_mctx.assign(*mvar1, val);
                    return unify_eqs(input_H, mvar2, num_eqs, updating, new_intros, subst);
                } catch (app_builder_exception & ex) {
                    throw_exception(mvar, "cases tactic failed, unexpected failure when using inverse");
                }
            } else {
                optional<name> c1 = is_gintro_rule_app(m_env, lhs);
                optional<name> c2 = is_gintro_rule_app(m_env, rhs);
                if (!c1 || !c2) {
                    auto s = mk_tactic_state(mvar);
                    throw cases_tactic_exception { s, [=] {
                            return format("cases tactic failed, unsupported equality between type and constructor indices") + line()
                                + format("(only equalities between constructors and/or variables are supported, try cases on the indices):") + line()
                                + s.pp_expr(H_type) + line();
                        }};
                }

                if (!is_constructor_app(m_env, lhs) || !is_constructor_app(m_env, rhs)) {
                    /* lhs or rhs is not a kernel constructor application,
                       that is, it is a generalized constructor generated by
                       the inductive compiler. */
                    if (*c1 == *c2) {
                        /*
                          lhs and rhs are of the form (C ...) where C is a generalized constructor.
                          We use the inj_arrow lemma to break equation into pieces.
                          We cannot use no_confusion because it would leak the internal encoding
                          used in the kernel.
                        */
                        A = whnf_ginductive(ctx, A);
                        expr const & A_fn   = get_app_fn(A);
                        if (!is_constant(A_fn) || !is_ginductive(m_env, const_name(A_fn)))
                            throw_ill_formed_datatype();
                        name inj_arrow_name = mk_injective_arrow_name(*c1);
                        optional<declaration> inj_arrow_decl = m_env.find(inj_arrow_name);
                        if (!inj_arrow_decl) {
                            throw exception(sstream() << "cases tactic failed, construction '"
                                            << inj_arrow_name << "' is not available in the environment");
                        }
                        unsigned inj_arrow_arity = get_arity(inj_arrow_decl->get_type());
                        expr target       = g1.get_type();
                        if (!ctx.is_prop(target)) {
                            /* TODO(Leo): refine this limitation.
                               Actually, we only need to disallow this case if the cases tactic
                               is being used by the equation compiler.
                               Reason: we don't have support for inj_arrow in the code that
                               generate proofs for equational lemmas produced by equational compiler.
                            */
                            throw exception(sstream() << "cases tactic failed, target is not a proposition, "
                                            "dependent elimination is currently not supported in this cases because one of the indices "
                                            "is an inductive datatype of '" << const_name(A_fn) << "', and this is a nested and/or mutually "
                                            "recursive datatype");
                        }
                        expr inj_arrow = mk_app(ctx, inj_arrow_name, inj_arrow_arity - 1, H, target);
                        lean_cases_trace(mvar, tout() << "injection\n";);
                        expr new_target = binding_domain(ctx.whnf(ctx.infer(inj_arrow)));
                        expr mvar2      = m_mctx.mk_metavar_decl(lctx, new_target);
                        expr val        = mk_app(inj_arrow, mvar2);
                        m_mctx.assign(*mvar1, val);
                        unsigned A_nparams = get_ginductive_num_params(m_env, const_name(A_fn));
                        lean_assert(get_app_num_args(lhs) >= A_nparams);
                        return unify_eqs(input_H, mvar2, num_eqs - 1 + get_app_num_args(lhs) - A_nparams,
                                         updating, new_intros, subst);
                    } else {
                        lean_assert(*c1 != *c2);
                        /*
                          lhs and rhs are generalized constructor applications, but with different constructors.
                          Thus, we normalize both of them to make sure we can use no_confusion
                        */
                        expr lhs_n = ctx.whnf(lhs);
                        expr rhs_n = ctx.whnf(rhs);
                        lean_assert(lhs != lhs_n || rhs != rhs_n);
                        expr new_eq     = ::lean::mk_eq(ctx, lhs_n, rhs_n);
                        expr new_target = mk_arrow(new_eq, binding_body(target));
                        expr new_mvar   = m_mctx.mk_metavar_decl(lctx, new_target);
                        m_mctx.assign(mvar, new_mvar);
                        lean_cases_trace(mvar, tout() << "normalize generalized constructors at lhs/rhs:\n" << pp_goal(mvar) << "\n";);
                        return unify_eqs(input_H, new_mvar, num_eqs, updating, new_intros, subst);
                    }
                } else {
                    /*
                      lhs and rhs are kernel constructor applications.
                      We use no_confusion to perform dependent elimination.
                    */
                    lean_assert(is_constructor_app(m_env, lhs));
                    lean_assert(is_constructor_app(m_env, rhs));
                    A = ctx.whnf(A);
                    buffer<expr> A_args;
                    expr const & A_fn   = get_app_args(A, A_args);
                    if (!is_constant(A_fn) || !inductive::is_inductive_decl(m_env, const_name(A_fn)))
                        throw_ill_formed_datatype();
                    name no_confusion_name(const_name(A_fn), "no_confusion");
                    if (!m_env.find(no_confusion_name)) {
                        throw exception(sstream() << "cases tactic failed, construction '"
                                        << no_confusion_name << "' is not available in the environment");
                    }
                    expr target       = g1.get_type();
                    level target_lvl  = get_level(ctx, target);
                    expr no_confusion = mk_app(mk_app(mk_constant(no_confusion_name, cons(target_lvl, const_levels(A_fn))),
                                                      A_args), target, lhs, rhs, H);
                    if (*c1 == *c2) {
                        lean_cases_trace(mvar, tout() << "injection\n";);
                        expr new_target = binding_domain(ctx.whnf(ctx.infer(no_confusion)));
                        expr mvar2      = m_mctx.mk_metavar_decl(lctx, new_target);
                        expr val        = mk_app(no_confusion, mvar2);
                        m_mctx.assign(*mvar1, val);
                        unsigned A_nparams = *inductive::get_num_params(m_env, const_name(A_fn));
                        lean_assert(get_app_num_args(lhs) >= A_nparams);
                        return unify_eqs(input_H, mvar2, num_eqs - 1 + get_app_num_args(lhs) - A_nparams,
                                         updating, new_intros, subst);
                    } else {
                        lean_assert(*c1 != *c2);
                        m_mctx.assign(*mvar1, no_confusion);
                        return none_expr();
                    }
                }
            }
        } else {
            throw_exception(mvar, "cases tactic failed, equality expected");
        }
    }

    pair<list<expr>, list<name>> unify_eqs(expr const & input_H, list<expr> const & mvars, list<name> const & cnames, unsigned num_eqs,
                                           intros_list * ilist, hsubstitution_list * slist) {
        lean_assert((ilist == nullptr) == (slist == nullptr));
        buffer<expr>              new_goals;
        buffer<list<expr>>        new_ilist;
        buffer<hsubstitution>     new_slist;
        buffer<name>              new_cnames;
        list<expr> it1            = mvars;
        list<name> itn            = cnames;
        intros_list const * it2   = ilist;
        hsubstitution_list const * it3 = slist;
        while (it1) {
            list<expr> new_intros;
            hsubstitution subst;
            if (ilist) {
                new_intros = head(*it2);
                subst      = head(*it3);
            }
            bool updating = ilist != nullptr;
            optional<expr> new_mvar = unify_eqs(input_H, head(it1), num_eqs, updating, new_intros, subst);
            if (new_mvar) {
                new_goals.push_back(*new_mvar);
                new_cnames.push_back(head(itn));
            }
            it1 = tail(it1);
            itn = tail(itn);
            if (ilist) {
                it2 = &tail(*it2);
                it3 = &tail(*it3);
                if (new_mvar) {
                    new_ilist.push_back(new_intros);
                    new_slist.push_back(subst);
                }
            }
        }
        if (ilist) {
            *ilist = to_list(new_ilist);
            *slist = to_list(new_slist);
        }
        return mk_pair(to_list(new_goals), to_list(new_cnames));
    }

    cases_tactic_fn(environment const & env, options const & opts, transparency_mode m,
                    metavar_context & mctx, list<name> & ids, bool unfold_ginductive):
        m_env(env),
        m_opts(opts),
        m_mode(m),
        m_mctx(mctx),
        m_ids(ids),
        m_unfold_ginductive(unfold_ginductive) {
    }

    pair<list<expr>, list<name>> operator()(expr const & mvar, expr const & H,
                                            intros_list * ilist, hsubstitution_list * slist) {
        lean_assert((ilist != nullptr) == (slist != nullptr));
        lean_assert(is_metavar(mvar));
        lean_assert(m_mctx.find_metavar_decl(mvar));
        if (!is_local(H))
            throw exception("cases tactic failed, argument must be a hypothesis");
        if (!is_cases_applicable(mvar, H))
            throw exception("cases tactic failed, it is not applicable to the given hypothesis");
        list<name> cname_list = get_ginductive_intro_rules(m_env, m_I_decl.get_name());
        metavar_decl g = m_mctx.get_metavar_decl(mvar);
        /* Remark: if ilist/rlist are provided, then we force dependent pattern matching
           even when indices are independent. */
        if (has_indep_indices(g, H) && (!slist || m_nindices == 0)) {
            /* Easy case */
            return mk_pair(induction(m_env, m_opts, m_mode, m_mctx, mvar, H,
                                     m_cases_on_decl.get_name(), m_ids,
                                     ilist, slist),
                           cname_list);
        } else {
            buffer<name> aux_indices_H; /* names of auxiliary indices and major  */
            unsigned num_eqs; /* number of equations that need to be processed */
            expr mvar1 = generalize_indices(mvar, H, aux_indices_H, num_eqs);
            lean_cases_trace(mvar1, tout() << "after generalize_indices:\n" << pp_goal(mvar1) << "\n";);
            expr H1    = m_mctx.get_metavar_decl(mvar1).get_context().get_last_local_decl().mk_ref();
            intros_list tmp_ilist;
            hsubstitution_list tmp_slist;
            list<expr> new_goals1 = induction(m_env, m_opts, m_mode, m_mctx, mvar1, H1, m_cases_on_decl.get_name(),
                                              m_ids, &tmp_ilist, &tmp_slist);
            lean_cases_trace(mvar1, tout() << "after applying cases_on:";
                             for (auto g : new_goals1) tout() << "\n" << pp_goal(g) << "\n";);
            list<expr> new_goals2 = elim_aux_indices(new_goals1, aux_indices_H, tmp_slist);
            if (ilist) {
                lean_assert(slist);
                *ilist = tmp_ilist;
                *slist = tmp_slist;
            }
            lean_cases_trace(mvar1, tout() << "after eliminating auxiliary indices:";
                             for (auto g : new_goals2) tout() << "\n" << pp_goal(g) << "\n";);
            return unify_eqs(H, new_goals2, cname_list, num_eqs, ilist, slist);
        }
    }
};

pair<list<expr>, list<name>>
cases(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
      expr const & mvar, expr const & H, list<name> & ids, intros_list * ilist, hsubstitution_list * slist,
      bool unfold_ginductive) {
    auto r = cases_tactic_fn(env, opts, m, mctx, ids, unfold_ginductive)(mvar, H, ilist, slist);
    lean_assert(length(r.first) == length(r.second));
    return r;
}

vm_obj tactic_cases_core(vm_obj const & H, vm_obj const & ns, vm_obj const & m, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    try {
        if (!s.goals()) return mk_no_goals_exception(s);
        list<name> ids       = to_list_name(ns);
        metavar_context mctx = s.mctx();
        list<list<expr>> hyps;
        hsubstitution_list substs;
        bool unfold_ginductive = false;
        pair<list<expr>, list<name>> info = cases(s.env(), s.get_options(), to_transparency_mode(m), mctx,
                                                  head(s.goals()), to_expr(H), ids, &hyps, &substs,
                                                  unfold_ginductive);
        list<name> constrs = info.second;
        buffer<vm_obj> info_objs;
        while (!is_nil(hyps)) {
            buffer<vm_obj> substs_objs;
            head(substs).for_each([&](name const & from, expr const & to) {
                    substs_objs.push_back(mk_vm_pair(to_obj(from), to_obj(to)));
                });
            info_objs.push_back(mk_vm_pair(to_obj(head(constrs)), mk_vm_pair(to_obj(head(hyps)), to_obj(substs_objs))));
            hyps    = tail(hyps);
            substs  = tail(substs);
            constrs = tail(constrs);
        }
        return tactic::mk_success(to_obj(info_objs), set_mctx_goals(s, mctx, append(info.first, tail(s.goals()))));
    } catch (cases_tactic_exception & ex) {
        return tactic::mk_exception(ex, ex.m_s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_cases_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "cases_core"}), tactic_cases_core);
    register_trace_class(name{"tactic", "cases"});
}

void finalize_cases_tactic() {
}
}
