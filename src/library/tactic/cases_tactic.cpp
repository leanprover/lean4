/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/trace.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/cases_tactic.h"
#include "library/tactic/intro_tactic.h"

namespace lean {
struct cases_tactic_fn {
    environment const &           m_env;
    options const &               m_opts;
    transparency_mode             m_mode;
    metavar_context &             m_mctx;
    /* User provided ids to name new hypotheses */
    list<name> &                  m_ids;

    /* Inductive datatype information */
    bool                          m_dep_elim;
    unsigned                      m_nparams;
    unsigned                      m_nindices;
    unsigned                      m_nminors;
    declaration                   m_I_decl;
    declaration                   m_cases_on_decl;

    type_context mk_type_context_for(metavar_decl const & g) {
        return ::lean::mk_type_context_for(m_env, m_opts, m_mctx, g.get_context(), m_mode);
    }

    type_context mk_type_context_for(expr const & mvar) {
        return mk_type_context_for(*m_mctx.get_metavar_decl(mvar));
    }

    #define lean_cases_trace(MVAR, CODE) lean_trace(name({"tactic", "cases"}), type_context TMP_CTX = mk_type_context_for(MVAR); scope_trace_env _scope1(m_env, TMP_CTX); CODE)

    void init_inductive_info(name const & n) {
        m_dep_elim       = inductive::has_dep_elim(m_env, n);
        m_nindices       = *inductive::get_num_indices(m_env, n);
        m_nparams        = *inductive::get_num_params(m_env, n);
        // This tactic is bases on cases_on construction which only has
        // minor premises for the introduction rules of this datatype.
        m_nminors        = *inductive::get_num_intro_rules(m_env, n);
        m_I_decl         = m_env.get(n);
        m_cases_on_decl  = m_env.get({n, "cases_on"});
    }

    bool is_cases_applicable(expr const & mvar, expr const & H) {
        type_context ctx = mk_type_context_for(mvar);
        expr t = ctx.infer(H);
        buffer<expr> args;
        expr const & fn = get_app_args(t, args);
        if (!is_constant(fn))
            return false;
        if (!inductive::is_inductive_decl(m_env, const_name(fn)))
            return false;
        if (!m_env.find(name{const_name(fn), "cases_on"}) || !m_env.find(get_eq_name()))
            return false;
        if (is_standard(m_env) && !m_env.find(get_heq_name()))
            return false;
        init_inductive_info(const_name(fn));
        if (args.size() != m_nindices + m_nparams)
            return false;
        lean_cases_trace(mvar, tout() << "inductive type: " << const_name(fn) << ", num. params: " << m_nparams << ", num. indices: " << m_nindices << "\n";);
        return true;
    }

    /** \brief We say h has independent indices IF
        1- it is *not* an indexed inductive family, OR
        2- it is an indexed inductive family, but all indices are distinct local constants,
        and all hypotheses of g different from h and indices, do not depend on the indices.
        3- if not m_dep_elim, then the conclusion does not depend on the indices. */
    bool has_indep_indices(metavar_decl const & g, expr const & h) {
        lean_assert(is_local(h));
        if (m_nindices == 0)
            return true;
        type_context ctx = mk_type_context_for(g);
        expr h_type = ctx.infer(h);
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
        if (!m_dep_elim) {
            expr const & g_type = g.get_type();
            if (depends_on(g_type, h))
                return false;
        }
        local_context lctx          = g.get_context();
        optional<local_decl> h_decl = lctx.get_local_decl(h);
        lean_assert(h_decl);
        bool ok = true;
        lctx.for_each_after(*h_decl, [&](local_decl const & h1) {
                if (!ok) return;
                /* h1 must not depend on the indices */
                if (depends_on(h1, m_nindices, args.end() - m_nindices))
                    ok = false;
            });
        return ok;
    }

    pair<expr, expr> mk_eq(type_context & ctx, expr const & lhs, expr const & rhs) {
        // make sure we don't assign regular metavars at is_def_eq
        type_context::tmp_mode_scope scope(ctx);
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

    [[ noreturn ]] void throw_ill_formed_datatype() {
        throw exception("tactic cases failed, unexpected inductive datatype type");
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
    expr generalize_indices(expr const & mvar, expr const & h) {
        lean_assert(is_standard(m_env));
        metavar_decl g     = *m_mctx.get_metavar_decl(mvar);
        type_context ctx   = mk_type_context_for(g);
        expr h_type        = ctx.infer(h);
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
        name h_new_name = ctx.lctx().get_unused_name(local_pp_name(h));
        expr h_new      = ctx.push_local(h_new_name, h_new_type);
        if (m_dep_elim)
            add_eq(h, h_new);
        /* aux_type is  Pi (j' : J) (h' : I A j'), j == j' -> h == h' -> T */
        expr aux_type   = ctx.mk_pi(ts, ctx.mk_pi(h_new, ctx.mk_pi(eqs, g.get_type())));
        expr aux_mvar   = m_mctx.mk_metavar_decl(g.get_context(), aux_type);
        /* assign mvar := aux_mvar indices h refls */
        m_mctx.assign(mvar, mk_app(mk_app(mk_app(aux_mvar, I_args.size() - m_nindices, I_args.end() - m_nindices), h), refls));
        /* introduce indices j' and h' */
        auto r = intron(m_env, m_opts, m_mctx, aux_mvar, m_nindices + 1);
        lean_assert(r);
        return *r;
    }

    format pp_goal(expr const & mvar) {
        tactic_state tmp(m_env, m_opts, m_mctx, to_list(mvar), mvar);
        return tmp.pp_goal(mvar);
    }

    cases_tactic_fn(environment const & env, options const & opts, transparency_mode m, metavar_context & mctx, list<name> & ids):
        m_env(env),
        m_opts(opts),
        m_mode(m),
        m_mctx(mctx),
        m_ids(ids) {
    }

    list<expr> operator()(expr const & mvar, expr const & H, intros_list * ilist, renaming_list * rlist) {
        lean_assert(is_metavar(mvar));
        lean_assert(m_mctx.get_metavar_decl(mvar));
        if (!is_local(H))
            throw exception("cases tactic failed, argumen must be a hypothesis");
        if (!is_cases_applicable(mvar, H))
            throw exception("cases tactic failed, it is not applicable to the given hypothesis");
        metavar_decl g = *m_mctx.get_metavar_decl(mvar);
        if (has_indep_indices(g, H)) {
            /* Easy case */
            return induction(m_env, m_opts, m_mode, m_mctx, mvar, H, m_cases_on_decl.get_name(), m_ids, ilist, rlist);
        } else {
            expr mvar1 = generalize_indices(mvar, H);
            lean_cases_trace(mvar1, tout() << "after generalize_indices:\n" << pp_goal(mvar1) << "\n";);
            lean_unreachable();
        }
    }
};

list<expr> cases(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
                 expr const & mvar, expr const & H, list<name> & ids,
                 intros_list * ilist, renaming_list * rlist) {
    return cases_tactic_fn(env, opts, m, mctx, ids)(mvar, H, ilist, rlist);
}

vm_obj tactic_cases_core(vm_obj const & m, vm_obj const & H, vm_obj const & ns, vm_obj const & _s) {
    tactic_state const & s   = to_tactic_state(_s);
    try {
        if (!s.goals()) return mk_no_goals_exception(s);
        list<name> ids       = to_list_name(ns);
        metavar_context mctx = s.mctx();
        list<expr> new_goals = cases(s.env(), s.get_options(), to_transparency_mode(m), mctx, head(s.goals()),
                                     to_expr(H), ids, nullptr, nullptr);
        return mk_tactic_success(set_mctx_goals(s, mctx, append(new_goals, tail(s.goals()))));
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

void initialize_cases_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "cases_core"}), tactic_cases_core);
    register_trace_class(name{"tactic", "cases"});
}

void finalize_cases_tactic() {
}
}
