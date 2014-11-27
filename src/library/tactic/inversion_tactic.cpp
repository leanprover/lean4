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
static bool is_inversion_applicable(environment const & env, expr const & t) {
    expr const & fn = get_app_fn(t);
    if (!is_constant(fn))
        return false;
    if (!inductive::is_inductive_decl(env, const_name(fn)))
        return false;
    if (!env.find(name{const_name(fn), "cases_on"}) ||
        !env.find(name("eq")) || !env.find(name("heq")))
        return false;
    return true;
}

static pair<expr, expr> mk_eq(type_checker & tc, expr const & lhs, expr const & rhs) {
    expr lhs_type = tc.infer(lhs).first;
    expr rhs_type = tc.infer(rhs).first;
    constraint_seq cs;
    if (tc.is_def_eq(lhs_type, rhs_type, justification(), cs) && !cs) {
        level l = sort_level(tc.ensure_type(lhs_type).first);
        return mk_pair(mk_app(mk_constant("eq", to_list(l)), lhs_type, lhs, rhs),
                       mk_app(mk_constant({"eq", "refl"}, to_list(l)), rhs_type, rhs));
    } else {
        level l = sort_level(tc.ensure_type(lhs_type).first);
        return mk_pair(mk_app(mk_constant("heq", to_list(l)), lhs_type, lhs, rhs_type, rhs),
                       mk_app(mk_constant({"heq", "refl"}, to_list(l)), rhs_type, rhs));
    }
}

tactic generalize_indices_tactic(name const & n) {
    auto fn = [=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
        goals const & gs  = s.get_goals();
        if (empty(gs))
            return none_proof_state();
        goal  g           = head(gs);
        goals tail_gs     = tail(gs);
        auto p = g.find_hyp(n);
        if (!p)
            return none_proof_state();
        expr const & h    = p->first;
        name_generator ngen = s.get_ngen();
        auto tc           = mk_type_checker(env, ngen.mk_child(), s.relax_main_opaque());
        expr h_type       = tc->whnf(mlocal_type(h)).first;
        if (!is_inversion_applicable(env, h_type))
            return none_proof_state();
        buffer<expr> hyps;
        g.get_hyps(hyps);
        expr m            = g.get_meta();
        expr m_type       = g.get_type();
        auto new_subst    = s.get_subst();
        name h_new_name   = g.get_unused_name(local_pp_name(h));
        buffer<expr> I_args;
        expr const & I    = get_app_args(h_type, I_args);
        // Set 1. generalize indices
        unsigned nindices = *inductive::get_num_indices(env, const_name(I));
        if (nindices > 0) {
            expr h_new_type  = mk_app(I, I_args.size() - nindices, I_args.data());
            expr d           = tc->whnf(tc->infer(h_new_type).first).first;
            unsigned eq_idx  = 1;
            name eq_prefix("H");
            buffer<expr> ts;
            buffer<expr> eqs;
            buffer<expr> refls;
            for (unsigned i = I_args.size() - nindices; i < I_args.size(); i++) {
                expr t_type = binding_domain(d);
                expr t      = mk_local(ngen.next(), g.get_unused_name(binding_name(d)), t_type, binder_info());
                expr const & index = I_args[i];
                pair<expr, expr> p = mk_eq(*tc, t, index);
                expr new_eq   = p.first;
                expr new_refl = p.second;
                eqs.push_back(mk_local(ngen.next(), g.get_unused_name(eq_prefix, eq_idx), new_eq, binder_info()));
                refls.push_back(new_refl);
                h_new_type  = mk_app(h_new_type, t);
                hyps.push_back(t);
                ts.push_back(t);
                d           = instantiate(binding_body(d), t);
            }
            expr h_new    = mk_local(ngen.next(), h_new_name, h_new_type, local_info(h));
            hyps.push_back(h_new);
            expr new_type = Pi(eqs, g.get_type());
            expr new_meta = mk_app(mk_metavar(ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            expr val      = g.abstract(mk_app(mk_app(mk_app(Fun(ts, Fun(h_new, new_meta)), nindices, I_args.end() - nindices), h), refls));
            new_subst.assign(g.get_name(), val);
            proof_state new_s(s, goals(new_g, tail_gs), new_subst, ngen);
            return some_proof_state(new_s);
        } else {
            expr h_new    = mk_local(ngen.next(), h_new_name, h_type, local_info(h));
            hyps.push_back(h_new);
            expr new_meta = mk_app(mk_metavar(ngen.next(), Pi(hyps, g.get_type())), hyps);
            goal new_g(new_meta, g.get_type());
            expr val      = g.abstract(mk_app(new_meta, h));
            new_subst.assign(g.get_name(), val);
            proof_state new_s(s, goals(new_g, tail_gs), new_subst, ngen);
            return some_proof_state(new_s);
        }
    };
    return tactic01(fn);
}

tactic cases_on_tactic() {
    // TODO(Leo)
    return id_tactic();
}

tactic inversion_eqs_tactic() {
    // TODO(Leo)
    return id_tactic();
}

tactic inversion_clear_tactic() {
    // TODO(Leo)
    return id_tactic();
}

tactic inversion_tactic(name const & n) {
    return generalize_indices_tactic(n) << cases_on_tactic() << inversion_eqs_tactic() << inversion_clear_tactic();
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
