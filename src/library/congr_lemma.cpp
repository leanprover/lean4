/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/congr_lemma.h"
#include "library/expr_unsigned_map.h"
#include "library/relation_manager.h"
#include "library/cache_helper.h"
#include "library/app_builder.h"
#include "library/fun_info.h"

namespace lean {
bool congr_lemma::all_eq_kind() const {
    return std::all_of(m_arg_kinds.begin(), m_arg_kinds.end(),
                       [](congr_arg_kind k) { return k == congr_arg_kind::Eq; });
}

struct congr_lemma_cache {
    typedef expr_unsigned_map<congr_lemma>  cache;
    environment          m_env;
    cache                m_simp_cache;
    cache                m_simp_cache_spec;
    cache                m_cache;
    cache                m_cache_spec;
    cache                m_hcache;
    congr_lemma_cache(environment const & env):
        m_env(env) {}
    environment const & env() const { return m_env; }
};

typedef cache_compatibility_helper<congr_lemma_cache> congr_lemma_cache_helper;

/* CACHE_RESET: YES */
MK_THREAD_LOCAL_GET_DEF(congr_lemma_cache_helper, get_clch);

congr_lemma_cache & get_congr_lemma_cache_for(type_context_old const & ctx) {
    return get_clch().get_cache_for(ctx);
}

struct congr_lemma_manager {
    typedef expr_unsigned key;
    typedef congr_lemma result;
    type_context_old &      m_ctx;
    congr_lemma_cache & m_cache;

    congr_lemma_manager(type_context_old & ctx):
        m_ctx(ctx), m_cache(get_congr_lemma_cache_for(ctx)) {}

    expr infer(expr const & e) { return m_ctx.infer(e); }
    expr whnf(expr const & e) { return m_ctx.whnf(e); }
    expr relaxed_whnf(expr const & e) { return m_ctx.relaxed_whnf(e); }

    /** \brief (Try to) cast expression \c e to the given type using the equations \c eqs.
        \c deps contains the indices of the relevant equalities.
        \remark deps is sorted. */
    expr cast(expr const & e, expr const & type, list<unsigned> const & deps, buffer<optional<expr>> const & eqs) {
        if (!deps)
            return e;
        unsigned d = head(deps);
        auto major = eqs[d];
        if (!major) {
            return cast(e, type, tail(deps), eqs);
        } else {
            expr lhs, rhs;
            lean_verify(is_eq(m_ctx.infer(*major), lhs, rhs));
            lean_assert(is_local(lhs));
            lean_assert(is_local(rhs));
            // We compute the new type by replacing rhs with lhs, and major with (refl lhs).
            expr motive, new_type;
            bool use_drec;
            if (depends_on(type, *major)) {
                // Since the type depends on the major, we must use dependent elimination.
                // and the motive just abstract rhs and *major
                use_drec  = true;
                motive    = m_ctx.mk_lambda({rhs, *major}, type);
                // We compute new_type by replacing rhs with lhs and *major with eq.refl(lhs) in type.
                new_type  = instantiate(abstract_local(type, rhs), lhs);
                expr refl = mk_eq_refl(m_ctx, lhs);
                new_type  = instantiate(abstract_local(new_type, *major), refl);
            } else {
                // type does not depend on the *major.
                // So, the motive is just (fun rhs, type), and
                // new_type just replaces rhs with lhs.
                use_drec = false;
                motive   = m_ctx.mk_lambda({rhs}, type);
                new_type = instantiate(abstract_local(type, rhs), lhs);
            }
            expr minor = cast(e, new_type, tail(deps), eqs);
            if (use_drec) {
                return mk_eq_drec(m_ctx, motive, minor, *major);
            } else {
                return mk_eq_rec(m_ctx, motive, minor, *major);
            }
        }
    }

    bool has_cast(buffer<congr_arg_kind> const & kinds) {
        return std::find(kinds.begin(), kinds.end(), congr_arg_kind::Cast) != kinds.end();
    }

    /** \brief Create simple congruence theorem using just congr, congr_arg, and congr_fun lemmas.
        \pre There are no "cast" arguments. */
    expr mk_simple_congr_proof(expr const & fn, buffer<expr> const & lhss,
                               buffer<optional<expr>> const & eqs, buffer<congr_arg_kind> const & kinds) {
        lean_assert(!has_cast(kinds));
        unsigned i = 0;
        for (; i < kinds.size(); i++) {
            if (kinds[i] != congr_arg_kind::Fixed)
                break;
        }
        expr g = mk_app(fn, i, lhss.data());
        if (i == kinds.size())
            return mk_eq_refl(m_ctx, g);
        lean_assert(kinds[i] == congr_arg_kind::Eq);
        lean_assert(eqs[i]);
        bool skip_arrow_test = true;
        expr pr = mk_congr_arg(m_ctx, g, *eqs[i], skip_arrow_test);
        i++;
        for (; i < kinds.size(); i++) {
            if (kinds[i] == congr_arg_kind::Eq) {
                bool skip_arrow_test = true;
                pr = ::lean::mk_congr(m_ctx, pr, *eqs[i], skip_arrow_test);
            } else {
                lean_assert(kinds[i] == congr_arg_kind::Fixed);
                pr = mk_congr_fun(m_ctx, pr, lhss[i]);
            }
        }
        return pr;
    }

    /** \brief Given a the set of hypotheses \c eqs, build a proof for <tt>lhs = rhs</tt> using \c eq.drec and \c eqs.
        \remark eqs are the proofs for the Eq arguments.
        \remark This is an auxiliary method used by mk_congr_simp. */
    expr mk_congr_proof(unsigned i, expr const & lhs, expr const & rhs, buffer<optional<expr>> const & eqs) {
        if (i == eqs.size()) {
            return mk_eq_refl(m_ctx, rhs);
        } else if (!eqs[i]) {
            return mk_congr_proof(i+1, lhs, rhs, eqs);
        } else {
            expr major = *eqs[i];
            expr x_1, x_2;
            lean_verify(is_eq(m_ctx.infer(major), x_1, x_2));
            lean_assert(is_local(x_1));
            lean_assert(is_local(x_2));
            expr motive_eq = mk_eq(m_ctx, lhs, rhs);
            expr motive    = m_ctx.mk_lambda({x_2, major}, motive_eq);
            // We compute the new_rhs by replacing x_2 with x_1 and major with (eq.refl x_1) in rhs.
            expr new_rhs = instantiate(abstract_local(rhs, x_2), x_1);
            expr x1_refl = mk_eq_refl(m_ctx, x_1);
            new_rhs      = instantiate(abstract_local(new_rhs, major), x1_refl);
            expr minor   = mk_congr_proof(i+1, lhs, new_rhs, eqs);
            return mk_eq_drec(m_ctx, motive, minor, major);
        }
    }

    void trace_too_many_arguments(expr const & fn, unsigned nargs) {
        lean_trace("congr_lemma", tout() << "failed to generate lemma for (" << fn << ") with " << nargs
                   << " arguments, too many arguments\n";);
    }

    void trace_app_builder_failure(expr const & fn) {
        lean_trace("congr_lemma", tout() << "failed to generate lemma for (" << fn << "), "
                   << " failed to build proof (enable 'trace.app_builder' for details)\n";);
    }

    /** \brief Create a congruence lemma that is useful for the simplifier.
        In this kind of lemma, if the i-th argument is a Cast argument, then the lemma
        contains an input a_i representing the i-th argument in the left-hand-side, and
        it appears with a cast (e.g., eq.drec ... a_i ...) in the right-hand-side.
        The idea is that the right-hand-side of this lemma "tells" the simplifier
        how the resulting term looks like. */
    optional<result> mk_congr_simp(expr const & fn, buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr fn_type = relaxed_whnf(infer(fn));
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;          // it contains the right-hand-side argument
            buffer<optional<expr>> eqs; // for Eq args, it contains the equality
            buffer<expr> hyps;          // contains lhss + rhss + eqs
            for (unsigned i = 0; i < pinfos.size(); i++) {
                if (!is_pi(fn_type)) {
                    trace_too_many_arguments(fn, pinfos.size());
                    return optional<result>();
                }
                expr lhs = locals.push_local_from_binding(fn_type);
                lhss.push_back(lhs);
                hyps.push_back(lhs);
                switch (kinds[i]) {
                case congr_arg_kind::Eq: {
                    expr rhs     = locals.push_local_from_binding(fn_type);
                    expr eq_type = mk_eq(m_ctx, lhs, rhs);
                    rhss.push_back(rhs);
                    expr eq = locals.push_local(e_name.append_after(eqs.size()+1), eq_type);
                    eqs.push_back(some_expr(eq));
                    hyps.push_back(rhs);
                    hyps.push_back(eq);
                    break;
                }
                case congr_arg_kind::HEq:
                    lean_unreachable();
                case congr_arg_kind::Fixed:
                    rhss.push_back(lhs);
                    eqs.push_back(none_expr());
                    break;
                case congr_arg_kind::FixedNoParam:
                    lean_unreachable(); // TODO(Leo): not implemented yet
                    break;
                case congr_arg_kind::Cast: {
                    expr rhs_type = m_ctx.infer(lhs);
                    rhs_type = instantiate_rev(abstract_locals(rhs_type, lhss.size()-1, lhss.data()),
                                               rhss.size(), rhss.data());
                    expr rhs = cast(lhs, rhs_type, pinfos[i].get_back_deps(), eqs);
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    break;
                }}
                fn_type  = relaxed_whnf(instantiate(binding_body(fn_type), lhs));
            }
            expr lhs = mk_app(fn, lhss);
            expr rhs = mk_app(fn, rhss);
            expr eq  = mk_eq(m_ctx, lhs, rhs);
            expr congr_type  = m_ctx.mk_pi(hyps, eq);
            expr congr_proof;
            if (has_cast(kinds)) {
                congr_proof = mk_congr_proof(0, lhs, rhs, eqs);
            } else {
                congr_proof = mk_simple_congr_proof(fn, lhss, eqs, kinds);
            }
            congr_proof = m_ctx.mk_lambda(hyps, congr_proof);
            return optional<result>(congr_type, congr_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            trace_app_builder_failure(fn);
            return optional<result>();
        }
    }

    /** \brief Create a congruence lemma for the congruence closure module.
        In this kind of lemma, if the i-th argument is a Cast argument, then the lemma
        contains two inputs a_i and b_i representing the i-th argument in the left-hand-side and
        right-hand-side.
        This lemma is based on the congruence lemma for the simplifier.
        It uses subsinglenton elimination to show that the congr-simp lemma right-hand-side
        is equal to the right-hand-side of this lemma. */
    optional<result> mk_congr(expr const & fn, optional<result> const & simp_lemma,
                              buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr fn_type1 = whnf(infer(fn));
            expr fn_type2 = fn_type1;
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;          // it contains the right-hand-side argument
            buffer<optional<expr>> eqs; // for Eq args, it contains the equality
            buffer<expr> hyps;          // contains lhss + rhss + eqs
            buffer<expr> simp_lemma_args;
            for (unsigned i = 0; i < pinfos.size(); i++) {
                if (!is_pi(fn_type1)) {
                    trace_too_many_arguments(fn, pinfos.size());
                    return optional<result>();
                }
                expr lhs = locals.push_local_from_binding(fn_type1);
                expr rhs;
                lhss.push_back(lhs);
                hyps.push_back(lhs);
                simp_lemma_args.push_back(lhs);
                switch (kinds[i]) {
                case congr_arg_kind::Eq: {
                    lean_assert(m_ctx.is_def_eq(binding_domain(fn_type1), binding_domain(fn_type2)));
                    rhs          = locals.push_local_from_binding(fn_type2);
                    expr eq_type = mk_eq(m_ctx, lhs, rhs);
                    rhss.push_back(rhs);
                    expr eq = locals.push_local(e_name.append_after(eqs.size()+1), eq_type);
                    eqs.push_back(some_expr(eq));
                    hyps.push_back(rhs);
                    hyps.push_back(eq);
                    simp_lemma_args.push_back(rhs);
                    simp_lemma_args.push_back(eq);
                    break;
                }
                case congr_arg_kind::HEq:
                    lean_unreachable();
                case congr_arg_kind::Fixed:
                    rhs = lhs;
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    break;
                case congr_arg_kind::FixedNoParam:
                    lean_unreachable(); // TODO(Leo): not implemented yet
                    break;
                case congr_arg_kind::Cast: {
                    rhs     = locals.push_local_from_binding(fn_type2);
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    hyps.push_back(rhs);
                    break;
                }}
                fn_type1  = whnf(instantiate(binding_body(fn_type1), lhs));
                fn_type2  = whnf(instantiate(binding_body(fn_type2), rhs));
            }
            expr fst   = mk_app(simp_lemma->get_proof(), simp_lemma_args);
            expr type1 = simp_lemma->get_type();
            while (is_pi(type1))
                type1 = binding_body(type1);
            type1      = instantiate_rev(type1, simp_lemma_args.size(), simp_lemma_args.data());
            expr lhs1, rhs1;
            lean_verify(is_eq(type1, lhs1, rhs1));
            // build proof2
            expr rhs2 = mk_app(fn, rhss);
            expr eq   = mk_eq(m_ctx, lhs1, rhs2);
            expr congr_type = m_ctx.mk_pi(hyps, eq);
            // build proof that rhs1 = rhs2
            unsigned i;
            for (i = 0; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast && !pinfos[i].is_prop())
                    break;
            }
            if (i == kinds.size()) {
                // rhs1 and rhs2 are definitionally equal
                expr congr_proof = m_ctx.mk_lambda(hyps, fst);
                return optional<result>(congr_type, congr_proof, to_list(kinds));
            }
            buffer<expr> rhss1;
            get_app_args_at_most(rhs1, rhss.size(), rhss1);
            lean_assert(rhss.size() == rhss1.size());
            expr a   = mk_app(fn, i, rhss1.data());
            expr snd = mk_eq_refl(m_ctx, a);
            for (; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast && !pinfos[i].is_prop()) {
                    expr r1   = rhss1[i];
                    expr r2   = rhss[i];
                    expr r1_eq_r2 = mk_app(m_ctx, get_subsingleton_elim_name(), r1, r2);
                    snd = ::lean::mk_congr(m_ctx, snd, r1_eq_r2);
                } else {
                    snd = mk_congr_fun(m_ctx, snd, rhss[i]);
                }
            }
            expr congr_proof = m_ctx.mk_lambda(hyps, mk_eq_trans(m_ctx, fst, snd));
            return optional<result>(congr_type, congr_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            trace_app_builder_failure(fn);
            return optional<result>();
        }
    }

    optional<result> mk_congr_simp(expr const & fn, unsigned nargs,
                                   fun_info const & finfo, ss_param_infos const & ssinfos) {
        auto r = m_cache.m_simp_cache.find(key(fn, nargs));
        if (r != m_cache.m_simp_cache.end())
            return optional<result>(r->second);
        list<unsigned> const & result_deps = finfo.get_result_deps();
        buffer<congr_arg_kind> kinds;
        buffer<param_info>     pinfos;
        buffer<ss_param_info>  ssinfos_buffer;
        to_buffer(finfo.get_params_info(), pinfos);
        to_buffer(ssinfos, ssinfos_buffer);
        kinds.resize(pinfos.size(), congr_arg_kind::Eq);
        for (unsigned i = 0; i < pinfos.size(); i++) {
            if (std::find(result_deps.begin(), result_deps.end(), i) != result_deps.end()) {
                kinds[i] = congr_arg_kind::Fixed;
            } else if (ssinfos_buffer[i].is_subsingleton()) {
                // See comment at mk_congr.
                if (!pinfos[i].is_prop() && pinfos[i].has_fwd_deps())
                    kinds[i] = congr_arg_kind::Fixed;
                else
                    kinds[i] = congr_arg_kind::Cast;
            } else if (pinfos[i].is_inst_implicit()) {
                lean_assert(!ssinfos_buffer[i].is_subsingleton());
                kinds[i] = congr_arg_kind::Fixed;
            }
        }
        for (unsigned i = 0; i < pinfos.size(); i++) {
            for (unsigned j = i+1; j < pinfos.size(); j++) {
                auto j_deps = pinfos[j].get_back_deps();
                if (std::find(j_deps.begin(), j_deps.end(), i) != j_deps.end() &&
                    kinds[j] == congr_arg_kind::Eq) {
                    // We must fix i because there is a j that depends on i,
                    // and j is not fixed nor a cast-fixed.
                    kinds[i] = congr_arg_kind::Fixed;
                    break;
                }
            }
        }
        auto new_r = mk_congr_simp(fn, pinfos, kinds);
        if (new_r) {
            m_cache.m_simp_cache.insert(mk_pair(key(fn, nargs), *new_r));
            return new_r;
        } else if (has_cast(kinds)) {
            // remove casts and try again
            for (unsigned i = 0; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast)
                    kinds[i] = congr_arg_kind::Fixed;
            }
            auto new_r = mk_congr_simp(fn, pinfos, kinds);
            if (new_r) {
                m_cache.m_simp_cache.insert(mk_pair(key(fn, nargs), *new_r));
                return new_r;
            } else {
                return new_r;
            }
        } else {
            return new_r;
        }
    }

    optional<result> mk_congr_simp(expr const & fn, unsigned nargs) {
        fun_info finfo         = get_fun_info(m_ctx, fn, nargs);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn, nargs);
        return mk_congr_simp(fn, nargs, finfo, ssinfos);
    }

    optional<result> mk_congr(expr const & fn, unsigned nargs,
                              fun_info const & finfo, ss_param_infos const & ssinfos) {
        auto r = m_cache.m_cache.find(key(fn, nargs));
        if (r != m_cache.m_cache.end())
            return optional<result>(r->second);
        optional<result> simp_lemma = mk_congr_simp(fn, nargs);
        if (!simp_lemma)
            return optional<result>();
        buffer<congr_arg_kind> kinds;
        buffer<param_info>     pinfos;
        buffer<ss_param_info>  ssinfos_buffer;
        to_buffer(simp_lemma->get_arg_kinds(), kinds);
        to_buffer(finfo.get_params_info(), pinfos);
        to_buffer(ssinfos, ssinfos_buffer);
        // For congr lemmas we have the following restriction:
        // if a Cast arg is subsingleton, it is not a proposition,
        // and it is a dependent argument, then we mark it as fixed.
        // This restriction doesn't affect the standard library,
        // but it simplifies the implementation.
        lean_assert(kinds.size() == pinfos.size());
        bool has_cast = false;
        for (unsigned i = 0; i < kinds.size(); i++) {
            if (!pinfos[i].is_prop() && ssinfos_buffer[i].is_subsingleton() && pinfos[i].has_fwd_deps()) {
                kinds[i] = congr_arg_kind::Fixed;
            }
            if (kinds[i] == congr_arg_kind::Cast)
                has_cast = true;
        }
        if (!has_cast) {
            m_cache.m_cache.insert(mk_pair(key(fn, nargs), *simp_lemma));
            return simp_lemma; // simp_lemma will be identical to regular congr lemma
        }
        auto new_r = mk_congr(fn, simp_lemma, pinfos, kinds);
        if (new_r)
            m_cache.m_cache.insert(mk_pair(key(fn, nargs), *new_r));
        return new_r;
    }

    void pre_specialize(expr const & a, expr & g, unsigned & prefix_sz, unsigned & num_rest_args) {
        ss_param_infos ssinfos = get_specialized_subsingleton_info(m_ctx, a);
        prefix_sz = 0;
        for (ss_param_info const & ssinfo : ssinfos) {
            if (!ssinfo.specialized())
                break;
            prefix_sz++;
        }
        num_rest_args = get_app_num_args(a) - prefix_sz;
        g = a;
        for (unsigned i = 0; i < num_rest_args; i++) {
            g = app_fn(g);
        }
    }

    result mk_specialize_result(result const & r, unsigned prefix_sz) {
        list<congr_arg_kind> new_arg_kinds = r.get_arg_kinds();
        for (unsigned i = 0; i < prefix_sz; i++)
            new_arg_kinds = cons(congr_arg_kind::FixedNoParam, new_arg_kinds);
        return result(r.get_type(), r.get_proof(), new_arg_kinds);
    }

    expr mk_hcongr_proof(expr type) {
        expr A, B, a, b;
        if (is_eq(type, a, b)) {
            return mk_eq_refl(m_ctx, a);
        } else if (is_heq(type, A, a, B, b)) {
            return mk_heq_refl(m_ctx, a);
        } else {
            type_context_old::tmp_locals locals(m_ctx);
            lean_assert(is_pi(type) && is_pi(binding_body(type)) && is_pi(binding_body(binding_body(type))));
            expr a      = locals.push_local_from_binding(type);
            type        = instantiate(binding_body(type), a);
            expr b      = locals.push_local_from_binding(type);
            expr motive = instantiate(binding_body(type), b);
            type        = instantiate(binding_body(type), a);
            expr eq_pr  = locals.push_local_from_binding(motive);
            type        = binding_body(type);
            motive      = binding_body(motive);
            lean_assert(closed(type) && closed(motive));
            expr minor  = mk_hcongr_proof(type);
            expr major  = eq_pr;
            if (is_heq(m_ctx.infer(eq_pr)))
                major  = mk_eq_of_heq(m_ctx, eq_pr);
            motive      = m_ctx.mk_lambda({b}, motive);
            return m_ctx.mk_lambda({a, b, eq_pr}, mk_eq_rec(m_ctx, motive, minor, major));
        }
    }

    optional<result> mk_hcongr_core(expr const & fn, unsigned nargs) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr fn_type_lhs = relaxed_whnf(infer(fn));
            expr fn_type_rhs = fn_type_lhs;
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;
            buffer<expr> eqs;
            buffer<expr> hyps;    // contains lhss + rhss + eqs
            buffer<congr_arg_kind> kinds;
            for (unsigned i = 0; i < nargs; i++) {
                if (!is_pi(fn_type_lhs)) {
                    trace_too_many_arguments(fn, nargs);
                    return optional<result>();
                }
                expr lhs = locals.push_local_from_binding(fn_type_lhs);
                lhss.push_back(lhs); hyps.push_back(lhs);
                expr rhs = locals.push_local(binding_name(fn_type_rhs).append_after("'"), binding_domain(fn_type_rhs));
                rhss.push_back(rhs); hyps.push_back(rhs);
                expr eq_type;
                expr domain_lhs = consume_auto_opt_param(binding_domain(fn_type_lhs));
                expr domain_rhs = consume_auto_opt_param(binding_domain(fn_type_rhs));
                if (domain_lhs == domain_rhs) {
                    eq_type = mk_eq(m_ctx, lhs, rhs);
                    kinds.push_back(congr_arg_kind::Eq);
                } else {
                    eq_type = mk_heq(m_ctx, lhs, rhs);
                    kinds.push_back(congr_arg_kind::HEq);
                }
                expr h_eq = locals.push_local(e_name.append_after(i), eq_type);
                eqs.push_back(h_eq); hyps.push_back(h_eq);
                fn_type_lhs  = relaxed_whnf(instantiate(binding_body(fn_type_lhs), lhs));
                fn_type_rhs  = relaxed_whnf(instantiate(binding_body(fn_type_rhs), rhs));
            }
            expr lhs = mk_app(fn, lhss);
            expr rhs = mk_app(fn, rhss);
            expr eq_type = mk_heq(m_ctx, lhs, rhs);
            expr result_type  = m_ctx.mk_pi(hyps, eq_type);
            expr result_proof = mk_hcongr_proof(result_type);
            return optional<result>(result_type, result_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            trace_app_builder_failure(fn);
            return optional<result>();
        }
    }

    optional<result> mk_congr_simp(expr const & fn) {
        fun_info finfo         = get_fun_info(m_ctx, fn);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn);
        return mk_congr_simp(fn, finfo.get_arity(), finfo, ssinfos);
    }

    optional<result> mk_specialized_congr_simp(expr const & a) {
        lean_assert(is_app(a));
        expr g; unsigned prefix_sz, num_rest_args;
        pre_specialize(a, g, prefix_sz, num_rest_args);
        key k(g, num_rest_args);
        auto it = m_cache.m_simp_cache_spec.find(k);
        if (it != m_cache.m_simp_cache_spec.end())
            return optional<result>(it->second);
        auto r = mk_congr_simp(g, num_rest_args);
        if (!r)
            return optional<result>();
        result new_r = mk_specialize_result(*r, prefix_sz);
        m_cache.m_simp_cache_spec.insert(mk_pair(k, new_r));
        return optional<result>(new_r);
    }

    optional<result> mk_congr(expr const & fn, unsigned nargs) {
        fun_info finfo = get_fun_info(m_ctx, fn, nargs);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn, nargs);
        return mk_congr(fn, nargs, finfo, ssinfos);
    }

    optional<result> mk_congr(expr const & fn) {
        fun_info finfo = get_fun_info(m_ctx, fn);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn);
        return mk_congr(fn, finfo.get_arity(), finfo, ssinfos);
    }

    optional<result> mk_specialized_congr(expr const & a) {
        lean_assert(is_app(a));
        expr g; unsigned prefix_sz, num_rest_args;
        pre_specialize(a, g, prefix_sz, num_rest_args);
        key k(g, num_rest_args);
        auto it = m_cache.m_cache_spec.find(k);
        if (it != m_cache.m_cache_spec.end())
            return optional<result>(it->second);
        auto r = mk_congr(g, num_rest_args);
        if (!r) {
            return optional<result>();
        }
        result new_r = mk_specialize_result(*r, prefix_sz);
        m_cache.m_cache_spec.insert(mk_pair(k, new_r));
        return optional<result>(new_r);
    }

    optional<result> mk_hcongr(expr const & fn, unsigned nargs) {
        auto r = m_cache.m_hcache.find(key(fn, nargs));
        if (r != m_cache.m_hcache.end())
            return optional<result>(r->second);
        auto new_r = mk_hcongr_core(fn, nargs);
        if (new_r)
            m_cache.m_hcache.insert(mk_pair(key(fn, nargs), *new_r));
        return new_r;
    }

    optional<result> mk_hcongr(expr const & fn) {
        fun_info finfo = get_fun_info(m_ctx, fn);
        return mk_hcongr(fn, finfo.get_arity());
    }
};

optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn) {
    return congr_lemma_manager(ctx).mk_congr_simp(fn);
}

optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn, unsigned nargs) {
    return congr_lemma_manager(ctx).mk_congr_simp(fn, nargs);
}

optional<congr_lemma> mk_specialized_congr_simp(type_context_old & ctx, expr const & a) {
    return congr_lemma_manager(ctx).mk_specialized_congr_simp(a);
}

optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn) {
    return congr_lemma_manager(ctx).mk_congr(fn);
}

optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn, unsigned nargs) {
    return congr_lemma_manager(ctx).mk_congr(fn, nargs);
}

optional<congr_lemma> mk_specialized_congr(type_context_old & ctx, expr const & a) {
    return congr_lemma_manager(ctx).mk_specialized_congr(a);
}

optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn) {
    return congr_lemma_manager(ctx).mk_hcongr(fn);
}

optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn, unsigned nargs) {
    return congr_lemma_manager(ctx).mk_hcongr(fn, nargs);
}

void initialize_congr_lemma() {
    register_trace_class("congr_lemma");
    register_thread_local_reset_fn([]() { get_clch().clear(); });
}
void finalize_congr_lemma() {
}
}
