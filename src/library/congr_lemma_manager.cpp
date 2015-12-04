/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/relation_manager.h"
#include "library/congr_lemma_manager.h"

namespace lean {
bool congr_lemma::all_eq_kind() const {
    return std::all_of(m_arg_kinds.begin(), m_arg_kinds.end(),
                       [](congr_arg_kind k) { return k == congr_arg_kind::Eq; });
}

struct congr_lemma_manager::imp {
    app_builder &      m_builder;
    fun_info_manager & m_fmanager;
    type_context &     m_ctx;
    struct key {
        expr         m_fn;
        unsigned     m_nargs;
        unsigned     m_hash;
        key(expr const & fn, unsigned nargs):
            m_fn(fn), m_nargs(nargs), m_hash(hash(m_fn.hash(), m_nargs)) {}
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.m_hash; }
    };

    struct key_eq_fn {
        bool operator()(key const & k1, key const & k2) const {
            return k1.m_fn == k2.m_fn && k1.m_nargs == k2.m_nargs;
        }
    };

    std::unordered_map<key, result, key_hash_fn, key_eq_fn> m_simp_cache;
    std::unordered_map<key, result, key_hash_fn, key_eq_fn> m_cache;
    std::unordered_map<key, result, key_hash_fn, key_eq_fn> m_rel_cache[2];
    relation_info_getter                                    m_relation_info_getter;

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
            lean_verify(is_eq(mlocal_type(*major), lhs, rhs));
            lean_assert(is_local(lhs));
            lean_assert(is_local(rhs));
            // We compute the new type by replacing rhs with lhs, and major with (refl lhs).
            expr motive, new_type;
            bool use_drec;
            if (depends_on(type, *major)) {
                // Since the type depends on the major, we must use dependent elimination.
                // and the motive just abstract rhs and *major
                use_drec  = true;
                motive    = Fun(rhs, Fun(*major, type));
                // We compute new_type by replacing rhs with lhs and *major with eq.refl(lhs) in type.
                new_type  = instantiate(abstract_local(type, rhs), lhs);
                expr refl = m_builder.mk_eq_refl(lhs);
                new_type  = instantiate(abstract_local(new_type, *major), refl);
            } else {
                // type does not depend on the *major.
                // So, the motive is just (fun rhs, type), and
                // new_type just replaces rhs with lhs.
                use_drec = false;
                motive   = Fun(rhs, type);
                new_type = instantiate(abstract_local(type, rhs), lhs);
            }
            expr minor = cast(e, new_type, tail(deps), eqs);
            if (use_drec) {
                return m_builder.mk_eq_drec(motive, minor, *major);
            } else {
                return m_builder.mk_eq_rec(motive, minor, *major);
            }
        }
    }

    bool has_cast(buffer<congr_arg_kind> const & kinds) {
        return std::find(kinds.begin(), kinds.end(), congr_arg_kind::Cast) != kinds.end();
    }

    expr mk_simple_congr_proof(expr const & fn, buffer<expr> const & lhss,
                               buffer<optional<expr>> const & eqs, buffer<congr_arg_kind> const & kinds) {
        unsigned i = 0;
        for (; i < kinds.size(); i++) {
            if (kinds[i] != congr_arg_kind::Fixed)
                break;
        }
        expr g = mk_app(fn, i, lhss.data());
        if (i == kinds.size())
            return m_builder.mk_eq_refl(g);
        lean_assert(kinds[i] == congr_arg_kind::Eq);
        lean_assert(eqs[i]);
        expr pr = m_builder.mk_congr_arg(g, *eqs[i]);
        i++;
        for (; i < kinds.size(); i++) {
            if (kinds[i] == congr_arg_kind::Eq) {
                pr = m_builder.mk_congr(pr, *eqs[i]);
            } else {
                lean_assert(kinds[i] == congr_arg_kind::Fixed);
                pr = m_builder.mk_congr_fun(pr, lhss[i]);
            }
        }
        return pr;
    }

    expr mk_congr_proof(unsigned i, expr const & lhs, expr const & rhs, buffer<optional<expr>> const & eqs) {
        if (i == eqs.size()) {
            return m_builder.mk_eq_refl(rhs);
        } else if (!eqs[i]) {
            return mk_congr_proof(i+1, lhs, rhs, eqs);
        } else {
            expr major = *eqs[i];
            expr x_1, x_2;
            lean_verify(is_eq(mlocal_type(major), x_1, x_2));
            lean_assert(is_local(x_1));
            lean_assert(is_local(x_2));
            expr motive_eq = m_builder.mk_eq(lhs, rhs);
            expr motive    = Fun(x_2, Fun(major, motive_eq));
            // We compute the new_rhs by replacing x_2 with x_1 and major with (eq.refl x_1) in rhs.
            expr new_rhs = instantiate(abstract_local(rhs, x_2), x_1);
            expr x1_refl = m_builder.mk_eq_refl(x_1);
            new_rhs      = instantiate(abstract_local(new_rhs, major), x1_refl);
            expr minor   = mk_congr_proof(i+1, lhs, new_rhs, eqs);
            return m_builder.mk_eq_drec(motive, minor, major);
        }
    }

    optional<result> mk_congr_simp(expr const & fn, buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        try {
            expr fn_type = whnf(infer(fn));
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;          // it contains the right-hand-side argument
            buffer<optional<expr>> eqs; // for Eq args, it contains the equality
            buffer<expr> hyps;          // contains lhss + rhss + eqs
            for (unsigned i = 0; i < pinfos.size(); i++) {
                if (!is_pi(fn_type)) {
                    return optional<result>();
                }
                expr lhs = m_ctx.mk_tmp_local(binding_name(fn_type), binding_domain(fn_type));
                lhss.push_back(lhs);
                hyps.push_back(lhs);
                switch (kinds[i]) {
                case congr_arg_kind::Eq: {
                    expr rhs     = m_ctx.mk_tmp_local(binding_name(fn_type), binding_domain(fn_type));
                    expr eq_type = m_builder.mk_eq(lhs, rhs);
                    rhss.push_back(rhs);
                    expr eq = m_ctx.mk_tmp_local(e_name.append_after(eqs.size()+1), eq_type);
                    eqs.push_back(some_expr(eq));
                    hyps.push_back(rhs);
                    hyps.push_back(eq);
                    break;
                }
                case congr_arg_kind::Fixed:
                    rhss.push_back(lhs);
                    eqs.push_back(none_expr());
                    break;
                case congr_arg_kind::Cast: {
                    expr rhs_type = mlocal_type(lhs);
                    rhs_type = instantiate_rev(abstract_locals(rhs_type, lhss.size()-1, lhss.data()), rhss.size(), rhss.data());
                    expr rhs = cast(lhs, rhs_type, pinfos[i].get_dependencies(), eqs);
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    break;
                }}
                fn_type  = whnf(instantiate(binding_body(fn_type), lhs));
            }
            expr lhs = mk_app(fn, lhss);
            expr rhs = mk_app(fn, rhss);
            expr eq  = m_builder.mk_eq(lhs, rhs);
            expr congr_type  = Pi(hyps, eq);
            expr congr_proof;
            if (has_cast(kinds)) {
                congr_proof = mk_congr_proof(0, lhs, rhs, eqs);
            } else {
                congr_proof = mk_simple_congr_proof(fn, lhss, eqs, kinds);
            }
            congr_proof = Fun(hyps, congr_proof);
            return optional<result>(congr_type, congr_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            return optional<result>();
        }
    }

    optional<result> mk_congr(expr const & fn, optional<result> const & simp_lemma,
                              buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        try {
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
                    return optional<result>();
                }
                expr lhs = m_ctx.mk_tmp_local(binding_name(fn_type1), binding_domain(fn_type1));
                expr rhs;
                lhss.push_back(lhs);
                hyps.push_back(lhs);
                simp_lemma_args.push_back(lhs);
                switch (kinds[i]) {
                case congr_arg_kind::Eq: {
                    lean_assert(m_ctx.is_def_eq(binding_domain(fn_type1), binding_domain(fn_type2)));
                    rhs          = m_ctx.mk_tmp_local(binding_name(fn_type2), binding_domain(fn_type2));
                    expr eq_type = m_builder.mk_eq(lhs, rhs);
                    rhss.push_back(rhs);
                    expr eq = m_ctx.mk_tmp_local(e_name.append_after(eqs.size()+1), eq_type);
                    eqs.push_back(some_expr(eq));
                    hyps.push_back(rhs);
                    hyps.push_back(eq);
                    simp_lemma_args.push_back(rhs);
                    simp_lemma_args.push_back(eq);
                    break;
                }
                case congr_arg_kind::Fixed:
                    rhs = lhs;
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    break;
                case congr_arg_kind::Cast: {
                    rhs     = m_ctx.mk_tmp_local(binding_name(fn_type2), binding_domain(fn_type2));
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    hyps.push_back(rhs);
                    break;
                }}
                fn_type1  = whnf(instantiate(binding_body(fn_type1), lhs));
                fn_type2  = whnf(instantiate(binding_body(fn_type2), rhs));
            }
            expr pr1   = mk_app(simp_lemma->get_proof(), simp_lemma_args);
            expr type1 = simp_lemma->get_type();
            while (is_pi(type1))
                type1 = binding_body(type1);
            type1      = instantiate_rev(type1, simp_lemma_args.size(), simp_lemma_args.data());
            expr lhs1, rhs1;
            lean_verify(is_eq(type1, lhs1, rhs1));
            // build proof2
            expr rhs2 = mk_app(fn, rhss);
            expr eq   = m_builder.mk_eq(lhs1, rhs2);
            expr congr_type = Pi(hyps, eq);
            // build proof that rhs1 = rhs2
            unsigned i;
            for (i = 0; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast && !pinfos[i].is_prop())
                    break;
            }
            if (i == kinds.size()) {
                // rhs1 and rhs2 are definitionally equal
                expr congr_proof = Fun(hyps, pr1);
                return optional<result>(congr_type, congr_proof, to_list(kinds));
            }
            buffer<expr> rhss1;
            get_app_args(rhs1, rhss1);
            lean_assert(rhss.size() == rhss1.size());
            expr a   = mk_app(fn, i, rhss1.data());
            expr pr2 = m_builder.mk_eq_refl(a);
            for (; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast && !pinfos[i].is_prop()) {
                    lean_assert(pinfos[i].is_subsingleton());
                    expr r1   = rhss1[i];
                    expr r2   = rhss[i];
                    expr r1_eq_r2 = m_builder.mk_app(get_subsingleton_elim_name(), r1, r2);
                    pr2 = m_builder.mk_congr(pr2, r1_eq_r2);
                } else {
                    pr2 = m_builder.mk_congr_fun(pr2, rhss[i]);
                }
            }
            expr congr_proof = Fun(hyps, m_builder.mk_eq_trans(pr1, pr2));
            return optional<result>(congr_type, congr_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            return optional<result>();
        }
    }

public:
    imp(app_builder & b, fun_info_manager & fm):
        m_builder(b), m_fmanager(fm), m_ctx(fm.ctx()),
        m_relation_info_getter(mk_relation_info_getter(fm.ctx().env())) {}

    type_context & ctx() { return m_ctx; }

    optional<result> mk_congr_simp(expr const & fn) {
        fun_info finfo = m_fmanager.get(fn);
        return mk_congr_simp(fn, finfo.get_arity());
    }

    optional<result> mk_congr_simp(expr const & fn, unsigned nargs) {
        auto r = m_simp_cache.find(key(fn, nargs));
        if (r != m_simp_cache.end())
            return optional<result>(r->second);
        fun_info finfo = m_fmanager.get(fn, nargs);
        list<unsigned> const & result_deps = finfo.get_dependencies();
        buffer<congr_arg_kind> kinds;
        buffer<param_info>     pinfos;
        to_buffer(finfo.get_params_info(), pinfos);
        kinds.resize(pinfos.size(), congr_arg_kind::Eq);
        for (unsigned i = 0; i < pinfos.size(); i++) {
            if (std::find(result_deps.begin(), result_deps.end(), i) != result_deps.end()) {
                kinds[i] = congr_arg_kind::Fixed;
            } else if (pinfos[i].is_subsingleton()) {
                // See comment at mk_congr.
                if (!pinfos[i].is_prop() && pinfos[i].is_dep())
                    kinds[i] = congr_arg_kind::Fixed;
                else
                    kinds[i] = congr_arg_kind::Cast;
            } else if (pinfos[i].is_inst_implicit()) {
                lean_assert(!pinfos[i].is_subsingleton());
                kinds[i] = congr_arg_kind::Fixed;
            }
        }
        for (unsigned i = 0; i < pinfos.size(); i++) {
            for (unsigned j = i+1; j < pinfos.size(); j++) {
                auto j_deps = pinfos[j].get_dependencies();
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
            m_simp_cache.insert(mk_pair(key(fn, nargs), *new_r));
            return new_r;
        } else if (has_cast(kinds)) {
            // remove casts and try again
            for (unsigned i = 0; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast)
                    kinds[i] = congr_arg_kind::Fixed;
            }
            auto new_r = mk_congr_simp(fn, pinfos, kinds);
            if (new_r) {
                m_simp_cache.insert(mk_pair(key(fn, nargs), *new_r));
                return new_r;
            } else {
                return new_r;
            }
        } else {
            return new_r;
        }
    }

    optional<result> mk_congr(expr const & fn) {
        fun_info finfo = m_fmanager.get(fn);
        return mk_congr(fn, finfo.get_arity());
    }

    optional<result> mk_congr(expr const & fn, unsigned nargs) {
        auto r = m_cache.find(key(fn, nargs));
        if (r != m_cache.end())
            return optional<result>(r->second);
        fun_info finfo = m_fmanager.get(fn, nargs);
        optional<result> simp_lemma = mk_congr_simp(fn, nargs);
        if (!simp_lemma)
            return optional<result>();
        buffer<congr_arg_kind> kinds;
        buffer<param_info>     pinfos;
        to_buffer(simp_lemma->get_arg_kinds(), kinds);
        to_buffer(finfo.get_params_info(), pinfos);
        // For congr lemmas we have the following restriction:
        // if a Cast arg is subsingleton, it is not a proposition,
        // and it is a dependent argument, then we mark it as fixed.
        // This restriction doesn't affect the standard library,
        // but it simplifies the implementation.
        lean_assert(kinds.size() == pinfos.size());
        bool has_cast = false;
        for (unsigned i = 0; i < kinds.size(); i++) {
            if (!pinfos[i].is_prop() && pinfos[i].is_subsingleton() && pinfos[i].is_dep()) {
                kinds[i] = congr_arg_kind::Fixed;
            }
            if (kinds[i] == congr_arg_kind::Cast)
                has_cast = true;
        }
        if (!has_cast) {
            m_cache.insert(mk_pair(key(fn, nargs), *simp_lemma));
            return simp_lemma; // simp_lemma will be identical to regular congr lemma
        }
        auto new_r = mk_congr(fn, simp_lemma, pinfos, kinds);
        if (new_r)
            m_cache.insert(mk_pair(key(fn, nargs), *new_r));
        return new_r;
    }

    optional<result> mk_rel_congr(expr const & R, bool is_iff) {
        try {
            if (!is_constant(R))
                return optional<result>();
            name const & R_name = const_name(R);
            auto info = m_relation_info_getter(R_name);
            if (!info)
                return optional<result>();
            unsigned arity = info->get_arity();
            key k(R, arity);
            auto r = m_rel_cache[is_iff].find(k);
            if (r != m_rel_cache[is_iff].end())
                return optional<result>(r->second);
            buffer<expr> hyps;
            buffer<congr_arg_kind> kinds;
            expr a1, b1, a2, b2;
            expr H1, H2;
            expr R_type = infer(R);
            for (unsigned i = 0; i < arity; i++) {
                R_type = relaxed_whnf(R_type);
                if (!is_pi(R_type))
                    return optional<result>();
                expr h = m_ctx.mk_tmp_local(binding_name(R_type), binding_domain(R_type));
                if (i == info->get_lhs_pos()) {
                    a1 = h;
                    a2 = m_ctx.mk_tmp_local(binding_name(R_type), binding_domain(R_type));
                    H1 = m_ctx.mk_tmp_local("H1", m_builder.mk_rel(R_name, a1, a2));
                    hyps.push_back(a1);
                    hyps.push_back(a2);
                    hyps.push_back(H1);
                    kinds.push_back(congr_arg_kind::Eq);
                } else if (i == info->get_rhs_pos()) {
                    b1 = h;
                    b2 = m_ctx.mk_tmp_local(binding_name(R_type), binding_domain(R_type));
                    H2 = m_ctx.mk_tmp_local("H2", m_builder.mk_rel(R_name, b1, b2));
                    hyps.push_back(b1);
                    hyps.push_back(b2);
                    hyps.push_back(H2);
                    kinds.push_back(congr_arg_kind::Eq);
                } else {
                    hyps.push_back(h);
                    kinds.push_back(congr_arg_kind::Fixed);
                }
                R_type = instantiate(binding_body(R_type), h);
            }
            expr lhs  = m_builder.mk_rel(R_name, a1, b1);
            expr rhs  = m_builder.mk_rel(R_name, a2, b2);
            //  (H1 : R a1 a2) -> (H2 : R b1 b2) -> (R a1 b1 <-> R a2 b2)
            expr type = is_iff ? m_builder.mk_iff(lhs, rhs) : m_builder.mk_eq(lhs, rhs);
            type = Pi(hyps, type);
            /* Proof:
               iff.intro
               (λ H : R a1 b1, trans (symm H1) (trans H H2))
               (λ H : R a2 b2, trans H1 (trans H (symm H2)))
            */
            expr H;
            H = m_ctx.mk_tmp_local(lhs);
            expr p1 = Fun(H, m_builder.mk_trans(R_name, m_builder.mk_symm(R_name, H1), m_builder.mk_trans(R_name, H, H2)));
            H = m_ctx.mk_tmp_local(rhs);
            expr p2 = Fun(H, m_builder.mk_trans(R_name, H1, m_builder.mk_trans(R_name, H, m_builder.mk_symm(R_name, H2))));
            expr pr = m_builder.mk_app(get_iff_intro_name(), p1, p2);
            if (!is_iff)
                pr = m_builder.mk_app(get_propext_name(), pr);
            pr = Fun(hyps, pr);
            result res(type, pr, to_list(kinds));
            m_rel_cache[is_iff].insert(mk_pair(k, res));
            return optional<result>(res);
        } catch (app_builder_exception &) {
            return optional<result>();
        }
    }

    optional<result> mk_rel_iff_congr(expr const & R) {
        return mk_rel_congr(R, true);
    }

    optional<result> mk_rel_eq_congr(expr const & R) {
        return mk_rel_congr(R, false);
    }
};

congr_lemma_manager::congr_lemma_manager(app_builder & b, fun_info_manager & fm):
    m_ptr(new imp(b, fm)) {
}

congr_lemma_manager::~congr_lemma_manager() {
}

type_context & congr_lemma_manager::ctx() { return m_ptr->ctx(); }

auto congr_lemma_manager::mk_congr_simp(expr const & fn) -> optional<result> {
    return m_ptr->mk_congr_simp(fn);
}
auto congr_lemma_manager::mk_congr_simp(expr const & fn, unsigned nargs) -> optional<result> {
    return m_ptr->mk_congr_simp(fn, nargs);
}
auto congr_lemma_manager::mk_congr(expr const & fn) -> optional<result> {
    return m_ptr->mk_congr(fn);
}
auto congr_lemma_manager::mk_congr(expr const & fn, unsigned nargs) -> optional<result> {
    return m_ptr->mk_congr(fn, nargs);
}

auto congr_lemma_manager::mk_rel_iff_congr(expr const & R) -> optional<result> {
    return m_ptr->mk_rel_iff_congr(R);
}

auto congr_lemma_manager::mk_rel_eq_congr(expr const & R) -> optional<result> {
    return m_ptr->mk_rel_eq_congr(R);
}
}
