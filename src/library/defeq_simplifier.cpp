/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/defeq_simplifier.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/tmp_type_context.h"
#include "library/normalize.h"

#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_SIMP_ROUNDS
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_SIMP_ROUNDS 5000
#endif
#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_REWRITE_ROUNDS
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_REWRITE_ROUNDS 5000
#endif
#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_TOP_DOWN
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_TOP_DOWN false
#endif
#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_EXHAUSTIVE
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_EXHAUSTIVE true
#endif
#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_MEMOIZE
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_MEMOIZE true
#endif

namespace lean {

/* Options */

static name * g_simplify_max_simp_rounds     = nullptr;
static name * g_simplify_max_rewrite_rounds  = nullptr;
static name * g_simplify_top_down            = nullptr;
static name * g_simplify_exhaustive          = nullptr;
static name * g_simplify_memoize             = nullptr;

static unsigned get_simplify_max_simp_rounds(options const & o) {
    return o.get_unsigned(*g_simplify_max_simp_rounds, LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_SIMP_ROUNDS);
}

static unsigned get_simplify_max_rewrite_rounds(options const & o) {
    return o.get_unsigned(*g_simplify_max_rewrite_rounds, LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_REWRITE_ROUNDS);
}

static bool get_simplify_top_down(options const & o) {
    return o.get_bool(*g_simplify_top_down, LEAN_DEFAULT_DEFEQ_SIMPLIFY_TOP_DOWN);
}

static bool get_simplify_exhaustive(options const & o) {
    return o.get_bool(*g_simplify_exhaustive, LEAN_DEFAULT_DEFEQ_SIMPLIFY_EXHAUSTIVE);
}

static bool get_simplify_memoize(options const & o) {
    return o.get_bool(*g_simplify_memoize, LEAN_DEFAULT_DEFEQ_SIMPLIFY_MEMOIZE);
}

/* Main simplifier class */

class defeq_simplify_fn {
    tmp_type_context_pool           & m_tmp_tctx_pool;
    tmp_type_context                * m_tmp_tctx;

    defeq_simp_lemmas                 m_simp_lemmas;

    unsigned                          m_num_simp_rounds{0};
    unsigned                          m_num_rewrite_rounds{0};

    /* Options */
    unsigned                          m_max_simp_rounds;
    unsigned                          m_max_rewrite_rounds;
    bool                              m_top_down;
    bool                              m_exhaustive;
    bool                              m_memoize;

    /* Cache */
    expr_struct_map<expr>             m_cache;

    optional<expr> cache_lookup(expr const & e) {
        auto it = m_cache.find(e);
        if (it == m_cache.end()) return none_expr();
        else return some_expr(it->second);
    }

    void cache_save(expr const & e, expr const & e_simp) {
        m_cache.insert(mk_pair(e, e_simp));
    }

    /* Simplification */
    expr defeq_simplify(expr const & _e) {
        expr e = _e;
        lean_trace_inc_depth("defeq_simplifier");
        lean_trace_d("defeq_simplifier", tout() << e << "\n";);

        while (true) {
            expr e_start = e;

            check_system("defeq_simplifier");
            m_num_simp_rounds++;
            if (m_num_simp_rounds > m_max_simp_rounds)
                throw exception("defeq_simplifier failed, maximum number of simp rounds exceeded");

            if (m_memoize) {
                if (auto it = cache_lookup(e)) return *it;
            }

            if (m_top_down) e = rewrite(whnf_eta(e));
            e = whnf_eta(e);

            switch (e.kind()) {
            case expr_kind::Local:
            case expr_kind::Meta:
            case expr_kind::Sort:
            case expr_kind::Constant:
                break;
            case expr_kind::Var:
                lean_unreachable();
            case expr_kind::Macro:
                e = defeq_simplify_macro(e);
                break;
            case expr_kind::Lambda:
                e = try_eta(defeq_simplify_binding(e));
                break;
            case expr_kind::Pi:
                e = defeq_simplify_binding(e);
                break;
            case expr_kind::App:
                e = defeq_simplify_app(e);
                break;
            case expr_kind::Let:
                lean_unreachable();
                // whnf expands let-expressions
            }
            if (!m_top_down) e = rewrite(whnf_eta(e));
            if (!m_exhaustive || e == e_start) break;
        }
        if (m_memoize) cache_save(_e, e);
        lean_assert(m_tmp_tctx->is_def_eq(_e, e));
        return e;
    }

    expr defeq_simplify_macro(expr const & e) {
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(defeq_simplify(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    expr defeq_simplify_binding(expr const & e) {
        expr d = defeq_simplify(binding_domain(e));
        expr l = m_tmp_tctx->mk_tmp_local(binding_name(e), d, binding_info(e));
        expr b = abstract(defeq_simplify(instantiate(binding_body(e), l)), l);
        return update_binding(e, d, b);
    }

    expr defeq_simplify_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args) {
            expr new_a = a;
            if (!m_tmp_tctx->is_prop(m_tmp_tctx->infer(a)))
                new_a = defeq_simplify(a);
            if (new_a != a)
                modified = true;
            a = new_a;
        }

        if (is_constant(f)) {
            if (auto idx = inductive::get_elim_major_idx(m_tmp_tctx->env(), const_name(f))) {
                if (auto r = normalizer(*m_tmp_tctx).unfold_recursor_major(f, *idx, args))
                    return *r;
            }
        }

        if (!modified)
            return e;

        expr r = mk_rev_app(f, args);

        if (is_constant(f) && m_tmp_tctx->env().is_recursor(const_name(f))) {
            return defeq_simplify(r);
        } else {
            return r;
        }
    }

    /* Rewriting */
    expr rewrite(expr const & _e) {
        expr e = _e;
        while (true) {
            check_system("defeq_simplifier");

            m_num_rewrite_rounds++;
            if (m_num_rewrite_rounds > m_max_rewrite_rounds)
                throw exception("defeq_simplifier failed, maximum number of rewrite rounds exceeded");

            list<defeq_simp_lemma> const * simp_lemmas_ptr = m_simp_lemmas.find(e);
            if (!simp_lemmas_ptr) return e;
            buffer<defeq_simp_lemma> simp_lemmas;
            to_buffer(*simp_lemmas_ptr, simp_lemmas);

            expr e_start = e;
            for (defeq_simp_lemma const & sl : simp_lemmas) e = rewrite(e, sl);
            if (e == e_start) break;
        }
        return e;
    }

    expr rewrite(expr const & e, defeq_simp_lemma const & sl) {
        tmp_type_context * tmp_tctx = m_tmp_tctx_pool.mk_tmp_type_context();
        tmp_tctx->clear();
        tmp_tctx->set_next_uvar_idx(sl.get_num_umeta());
        tmp_tctx->set_next_mvar_idx(sl.get_num_emeta());

        if (!tmp_tctx->is_def_eq(e, sl.get_lhs())) return e;

        lean_trace(name({"defeq_simplifier", "rewrite"}),
                   expr new_lhs = tmp_tctx->instantiate_uvars_mvars(sl.get_lhs());
                   expr new_rhs = tmp_tctx->instantiate_uvars_mvars(sl.get_rhs());
                   tout() << "(" << sl.get_id() << ") "
                   << "[" << new_lhs << " --> " << new_rhs << "]\n";);

        if (!instantiate_emetas(tmp_tctx, sl.get_emetas(), sl.get_instances())) return e;

        for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
            if (!tmp_tctx->is_uvar_assigned(i)) return e;
        }

        expr new_rhs = tmp_tctx->instantiate_uvars_mvars(sl.get_rhs());
        m_tmp_tctx_pool.recycle_tmp_type_context(tmp_tctx);
        return new_rhs;
    }


    bool instantiate_emetas(tmp_type_context * tmp_tctx, list<expr> const & _emetas, list<bool> const & _instances) {
        buffer<expr> emetas;
        buffer<bool> instances;
        to_buffer(_emetas, emetas);
        to_buffer(_instances, instances);

        lean_assert(emetas.size() == instances.size());
        for (unsigned i = 0; i < emetas.size(); ++i) {
            expr m = emetas[i];
            unsigned mvar_idx = emetas.size() - 1 - i;
            expr m_type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));
            lean_assert(!has_metavar(m_type));
            if (tmp_tctx->is_mvar_assigned(mvar_idx)) continue;
            if (instances[i]) {
                if (auto v = tmp_tctx->mk_class_instance(m_type)) {
                    if (!tmp_tctx->assign(m, *v)) {
                        lean_trace(name({"defeq_simplifier", "failure"}),
                                   tout() << "unable to assign instance for: " << m_type << "\n";);
                        return false;
                    } else {
                        lean_assert(tmp_tctx->is_mvar_assigned(mvar_idx));
                        continue;
                    }
                } else {
                    lean_trace(name({"defeq_simplifier", "failure"}),
                               tout() << "unable to synthesize instance for: " << m_type << "\n";);
                    return false;
                }
            } else {
                lean_trace(name({"defeq_simplifier", "failure"}),
                           tout() << "failed to assign: " << m << " : " << m_type << "\n";);
                return false;
            }
        }
        return true;
    }

    expr whnf_eta(expr const & e) {
        return try_eta(m_tmp_tctx->whnf(e));
    }

public:
    defeq_simplify_fn(tmp_type_context_pool & tmp_tctx_pool, options const & o, defeq_simp_lemmas const & simp_lemmas):
        m_tmp_tctx_pool(tmp_tctx_pool),
        m_tmp_tctx(m_tmp_tctx_pool.mk_tmp_type_context()),
        m_simp_lemmas(simp_lemmas),
        m_max_simp_rounds(get_simplify_max_simp_rounds(o)),
        m_max_rewrite_rounds(get_simplify_max_rewrite_rounds(o)),
        m_top_down(get_simplify_top_down(o)),
        m_exhaustive(get_simplify_exhaustive(o)),
        m_memoize(get_simplify_memoize(o))
        { }

    ~defeq_simplify_fn() {
        m_tmp_tctx_pool.recycle_tmp_type_context(m_tmp_tctx);
    }
    expr operator()(expr const & e)  { return defeq_simplify(e); }
};

/* Setup and teardown */

void initialize_defeq_simplifier() {
    register_trace_class("defeq_simplifier");
    register_trace_class(name({"defeq_simplifier", "rewrite"}));
    register_trace_class(name({"defeq_simplifier", "failure"}));

    g_simplify_max_simp_rounds    = new name{"defeq_simplify", "max_simp_rounds"};
    g_simplify_max_rewrite_rounds = new name{"defeq_simplify", "max_rewrite_rounds"};
    g_simplify_top_down           = new name{"defeq_simplify", "top_down"};
    g_simplify_exhaustive         = new name{"defeq_simplify", "exhaustive"};
    g_simplify_memoize            = new name{"defeq_simplify", "memoize"};

    register_unsigned_option(*g_simplify_max_simp_rounds, LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_SIMP_ROUNDS,
                             "(defeq_simplify) max allowed simplification rounds");
    register_unsigned_option(*g_simplify_max_rewrite_rounds, LEAN_DEFAULT_DEFEQ_SIMPLIFY_MAX_REWRITE_ROUNDS,
                             "(defeq_simplify) max allowed rewrite rounds");
    register_bool_option(*g_simplify_top_down, LEAN_DEFAULT_DEFEQ_SIMPLIFY_TOP_DOWN,
                         "(defeq_simplify) use top-down rewriting instead of bottom-up");
    register_bool_option(*g_simplify_exhaustive, LEAN_DEFAULT_DEFEQ_SIMPLIFY_EXHAUSTIVE,
                         "(defeq_simplify) simplify exhaustively");
    register_bool_option(*g_simplify_memoize, LEAN_DEFAULT_DEFEQ_SIMPLIFY_MEMOIZE,
                         "(defeq_simplify) memoize simplifications");
}

void finalize_defeq_simplifier() {
    delete g_simplify_memoize;
    delete g_simplify_exhaustive;
    delete g_simplify_top_down;
    delete g_simplify_max_rewrite_rounds;
    delete g_simplify_max_simp_rounds;
}

/* Entry point */
expr defeq_simplify(tmp_type_context_pool & tmp_tctx_pool, options const & o, defeq_simp_lemmas const & simp_lemmas, expr const & e) {
    return defeq_simplify_fn(tmp_tctx_pool, o, simp_lemmas)(e);
}

}
