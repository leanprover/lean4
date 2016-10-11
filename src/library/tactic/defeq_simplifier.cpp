/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/fun_info.h"
#include "library/defeq_canonizer.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/simp_lemmas_tactics.h"
#include "library/tactic/defeq_simplifier.h"

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
#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS false
#endif

namespace lean {

/* Options */

static name * g_simplify_max_simp_rounds     = nullptr;
static name * g_simplify_max_rewrite_rounds  = nullptr;
static name * g_simplify_top_down            = nullptr;
static name * g_simplify_exhaustive          = nullptr;
static name * g_simplify_memoize             = nullptr;
static name * g_simplify_canonize_proofs     = nullptr;

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

static bool get_simplify_canonize_proofs(options const & o) {
    return o.get_bool(*g_simplify_canonize_proofs, LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS);
}

/* Main simplifier class */
class defeq_simplify_fn {
    type_context           & m_ctx;

    simp_lemmas_for          m_simp_lemmas;

    unsigned                 m_num_simp_rounds{0};
    unsigned                 m_num_rewrite_rounds{0};

    bool                     m_need_restart;

    /* Options */
    unsigned                 m_max_simp_rounds;
    unsigned                 m_max_rewrite_rounds;
    bool                     m_top_down;
    bool                     m_exhaustive;
    bool                     m_memoize;
    bool                     m_canonize_proofs;

    /* Cache */
    expr_struct_map<expr>    m_cache;

    optional<expr> cache_lookup(expr const & e) {
        auto it = m_cache.find(e);
        if (it == m_cache.end()) return none_expr();
        else return some_expr(it->second);
    }

    void cache_save(expr const & e, expr const & e_simp) {
        m_cache.insert(mk_pair(e, e_simp));
    }

    environment const & env() const { return m_ctx.env(); }

    /* Simplification */
    expr defeq_simplify(expr const & _e) {
        expr e = _e;
        lean_trace_inc_depth("defeq_simplifier");
        lean_trace_d("defeq_simplifier", tout() << e << "\n";);

        while (true) {
            expr e_start = e;

            check_system("defeq_simplifier");
            m_num_simp_rounds++;
            if (m_num_simp_rounds > m_max_simp_rounds) {
                throw defeq_simplifier_exception(sstream() <<
                                                 "defeq simplifier failed, maximum number of simp rounds exceeded "
                                                 "(possible solution: increase limit using "
                                                 "`set_option defeq_simplify.max_simp_rounds <limit>`, "
                                                 "the current limit is " << m_max_simp_rounds << ") "
                                                 "(use `set_option trace.defeq_simplifier true` to obtain more information");
            }
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
        expr l = m_ctx.push_local(binding_name(e), d, binding_info(e));
        expr b = defeq_simplify(instantiate(binding_body(e), l));
        b = m_ctx.abstract_locals(b, 1, &l);
        m_ctx.pop_local();
        return update_binding(e, d, b);
    }

    expr defeq_simplify_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f        = get_app_args(e, args);
        fun_info info = get_fun_info(m_ctx, f, args.size());
        unsigned i    = 0;
        for (param_info const & pinfo : info.get_params_info()) {
            lean_assert(i < args.size());
            expr new_a;
            if (pinfo.is_inst_implicit() || (m_canonize_proofs && pinfo.is_prop())) {
                new_a = defeq_canonize(m_ctx, args[i], m_need_restart);
                lean_trace(name({"defeq_simplifier", "canonize"}),
                           tout() << "\n" << args[i] << "\n===>\n" << new_a << "\n";);
            } else if (pinfo.is_prop()) {
                /* TODO(Leo): should we also ignore subsingletons */
                /* Ignore propositions */
                new_a = args[i];
            } else {
                new_a = defeq_simplify(args[i]);
            }
            if (new_a != args[i])
                modified = true;
            args[i] = new_a;
            i++;
        }
        for (; i < args.size(); i++) {
            expr new_a = defeq_simplify(args[i]);
            if (new_a != args[i])
                modified = true;
            args[i] = new_a;
        }

        /*
        if (is_constant(f)) {
            if (auto idx = inductive::get_elim_major_idx(m_tmp_tctx->env(), const_name(f))) {
                if (auto r = normalizer(*m_tmp_tctx).unfold_recursor_major(f, *idx, args))
                    return *r;
            }
        }
        */

        if (!modified)
            return e;

        expr r = mk_app(f, args);

        if (is_constant(f) && env().is_recursor(const_name(f))) {
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
            if (m_num_rewrite_rounds > m_max_rewrite_rounds) {
                throw defeq_simplifier_exception(sstream() <<
                                                 "defeq simplifier failed, maximum number of rewrite rounds exceeded "
                                                 "(possible solution: increase limit using "
                                                 "`set_option defeq_simplify.max_rewrite_rounds <limit>`, "
                                                 "the current limit is " << m_max_rewrite_rounds << ") "
                                                 "(use `set_option trace.defeq_simplifier true` to obtain more information");
            }
            list<simp_lemma> const * simp_lemmas_ptr = m_simp_lemmas.find(e);
            if (!simp_lemmas_ptr) return e;
            buffer<simp_lemma> simp_lemmas;
            to_buffer(*simp_lemmas_ptr, simp_lemmas);

            expr e_start = e;
            for (simp_lemma const & sl : simp_lemmas) {
                if (sl.is_refl())
                    e = rewrite(e, sl);
            }
            if (e == e_start) break;
        }
        return e;
    }

    expr rewrite(expr const & e, simp_lemma const & sl) {
        return refl_lemma_rewrite(m_ctx, e, sl);
    }

    expr whnf_eta(expr const & e) {
        return try_eta(m_ctx.whnf(e));
    }

public:
    defeq_simplify_fn(type_context & ctx, simp_lemmas const & simp_lemmas):
        m_ctx(ctx),
        m_max_simp_rounds(get_simplify_max_simp_rounds(ctx.get_options())),
        m_max_rewrite_rounds(get_simplify_max_rewrite_rounds(ctx.get_options())),
        m_top_down(get_simplify_top_down(ctx.get_options())),
        m_exhaustive(get_simplify_exhaustive(ctx.get_options())),
        m_memoize(get_simplify_memoize(ctx.get_options())),
        m_canonize_proofs(get_simplify_canonize_proofs(ctx.get_options())) {
        if (auto * s = simp_lemmas.find(get_eq_name()))
            m_simp_lemmas = *s;
    }

    ~defeq_simplify_fn() {}

    expr operator()(expr e) {
        scope_trace_env scope(env(), m_ctx);
        while (true) {
            m_need_restart = false;
            e = defeq_simplify(e);
            if (!m_need_restart)
                return e;
            m_cache.clear();
        }
    }
};

/* Entry point */
expr defeq_simplify(type_context & ctx, simp_lemmas const & simp_lemmas, expr const & e) {
    return defeq_simplify_fn(ctx, simp_lemmas)(e);
}

vm_obj simp_lemmas_dsimplify_core(vm_obj const & m, vm_obj const & _lemmas, vm_obj const & e, vm_obj const & s0) {
    type_context ctx = mk_type_context_for(s0, m);
    tactic_state const & s    = to_tactic_state(s0);
    LEAN_TACTIC_TRY;
    simp_lemmas lemmas = to_simp_lemmas(_lemmas);
    expr new_e         = defeq_simplify(ctx, lemmas, to_expr(e));
    return mk_tactic_success(to_obj(new_e), s);
    LEAN_TACTIC_CATCH(s);
}

expr defeq_simplify(type_context & ctx, expr const & e) {
    simp_lemmas lemmas  = get_default_simp_lemmas(ctx.env(), transparency_mode::Reducible);
    return defeq_simplify(ctx, lemmas, e);
}

/* Setup and teardown */
void initialize_defeq_simplifier() {
    DECLARE_VM_BUILTIN(name({"simp_lemmas", "dsimplify_core"}), simp_lemmas_dsimplify_core);

    register_trace_class("defeq_simplifier");
    register_trace_class(name({"defeq_simplifier", "canonize"}));

    g_simplify_max_simp_rounds    = new name{"defeq_simplify", "max_simp_rounds"};
    g_simplify_max_rewrite_rounds = new name{"defeq_simplify", "max_rewrite_rounds"};
    g_simplify_top_down           = new name{"defeq_simplify", "top_down"};
    g_simplify_exhaustive         = new name{"defeq_simplify", "exhaustive"};
    g_simplify_memoize            = new name{"defeq_simplify", "memoize"};
    g_simplify_canonize_proofs    = new name{"defeq_simplify", "canonize_proofs"};

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
    register_bool_option(*g_simplify_canonize_proofs, LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS,
                         "(defeq_simplify) use type class instance canonizer to canonize proofs too");
}

void finalize_defeq_simplifier() {
    delete g_simplify_memoize;
    delete g_simplify_exhaustive;
    delete g_simplify_top_down;
    delete g_simplify_max_rewrite_rounds;
    delete g_simplify_max_simp_rounds;
    delete g_simplify_canonize_proofs;
}
}
