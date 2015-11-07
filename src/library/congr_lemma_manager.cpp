/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/replace_visitor.h"
#include "library/congr_lemma_manager.h"

namespace lean {
class congr_lemma_manager::imp {
    app_builder &      m_builder;
    fun_info_manager & m_fmanager;
    type_context &     m_ctx;
    struct key {
        expr const & m_fn;
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

    std::unordered_map<key, result, key_hash_fn, key_eq_fn> m_cache;

    struct failure {
        unsigned m_arg_idx;
        failure(unsigned i):m_arg_idx(i) {}
    };

    expr infer(expr const & e) { return m_ctx.infer(e); }
    expr whnf(expr const & e) { return m_ctx.whnf(e); }

    /** \brief (Try to) cast expression \c e to the given type using the equations \c eqs.
        \c deps contains the indices of the relevant equalities.
        \remark deps is sorted. */
    optional<expr> cast(expr const & e, expr const & type, list<unsigned> const & deps, buffer<optional<expr>> const & eqs) {
        if (!deps)
            return some_expr(e);
        unsigned d = head(deps);
        auto major = eqs[d];
        if (!major) {
            return cast(e, type, tail(deps), eqs);
        } else {
            expr lhs, rhs;
            lean_verify(is_eq(mlocal_type(*major), lhs, rhs));
            lean_assert(is_local(lhs));
            lean_assert(is_local(rhs));
            // We compute the motive by replacing rhs with the fresh local x,
            // and major with fresh local H.
            // We compute the new type by replacing rhs with lhs, and major with (refl lhs).
            expr motive, new_type;
            bool use_drec;
            if (depends_on(type, *major)) {
                // Since the type depends on the major, we must use dependent elimination.
                // and the motive just abstract rhs and *major
                use_drec  = true;
                motive    = Fun(rhs, Fun(*major, type));
                // We compute new_type by replacing rhs with lhs and *major with eq.refl(lhs) in type.
                new_type  = instantiate(abstract(type, rhs), lhs);
                auto refl = m_builder.mk_eq_refl(lhs);
                if (!refl)
                    return none_expr();
                new_type  = instantiate(abstract(new_type, *major), *refl);
            } else {
                // type does not depend on the *major.
                // So, the motive is just (fun rhs, type), and
                // new_type just replaces rhs with lhs.
                use_drec = false;
                motive   = Fun(rhs, type);
                new_type = instantiate(abstract(type, rhs), lhs);
            }
            auto minor = cast(e, new_type, tail(deps), eqs);
            if (!minor)
                return none_expr();
            if (use_drec) {
                return m_builder.mk_eq_drec(motive, *minor, *major);
            } else {
                return m_builder.mk_eq_rec(motive, *minor, *major);
            }
        }
    }

    optional<result> mk_congr_simp(expr const & fn, buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        for (unsigned i = 0; i < kinds.size(); i++)
            std::cout << (unsigned)kinds[i] << " ";
        std::cout << "\n";

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
                expr rhs = m_ctx.mk_tmp_local(binding_name(fn_type), binding_domain(fn_type));
                expr eq_type;
                if (auto it = m_builder.mk_eq(lhs, rhs))
                    eq_type = *it;
                else
                    return optional<result>();
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
                auto rhs = cast(lhs, rhs_type, pinfos[i].get_dependencies(), eqs);
                if (!rhs) {
                    return optional<result>();
                }
                rhss.push_back(*rhs);
                eqs.push_back(none_expr());
                break;
            }}
            // std::cout << lhss.back() << "\n";
            // std::cout << rhss.back() << "\n\n";
            fn_type  = whnf(instantiate(binding_body(fn_type), lhs));
        }
        expr lhs = mk_app(fn, lhss);
        expr rhs = mk_app(fn, rhss);
        auto eq  = m_builder.mk_eq(lhs, rhs);
        if (!eq)
            return optional<result>();
        expr congr_type  = Pi(hyps, *eq);
        auto congr_proof = m_builder.mk_sorry(congr_type);
        if (!congr_proof)
            return optional<result>();
        return optional<result>(congr_type, *congr_proof, to_list(kinds));
    }

public:
    imp(app_builder & b, fun_info_manager & fm):
        m_builder(b), m_fmanager(fm), m_ctx(fm.ctx()) {}

    optional<result> mk_congr_simp(expr const & fn) {
        fun_info finfo = m_fmanager.get(fn);
        return mk_congr_simp(fn, finfo.get_arity());
    }

    optional<result> mk_congr_simp(expr const & fn, unsigned nargs) {
        auto r = m_cache.find(key(fn, nargs));
        if (r != m_cache.end())
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
                if (empty(pinfos[i].get_dependencies()))
                    kinds[i] = congr_arg_kind::Fixed;
                else
                    kinds[i] = congr_arg_kind::Cast;
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
        while (true) {
            try {
                auto new_r = mk_congr_simp(fn, pinfos, kinds);
                if (new_r)
                    m_cache.insert(mk_pair(key(fn, nargs), *new_r));
                return new_r;
            } catch (failure & ex) {
                kinds[ex.m_arg_idx] = congr_arg_kind::Fixed;
            }
        }
    }
};

congr_lemma_manager::congr_lemma_manager(app_builder & b, fun_info_manager & fm):
    m_ptr(new imp(b, fm)) {
}

congr_lemma_manager::~congr_lemma_manager() {
}

auto congr_lemma_manager::mk_congr_simp(expr const & fn) -> optional<result> {
    return m_ptr->mk_congr_simp(fn);
}
auto congr_lemma_manager::mk_congr_simp(expr const & fn, unsigned nargs) -> optional<result> {
    return m_ptr->mk_congr_simp(fn, nargs);
}
}
