/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <functional>
#include <iostream>
#include "util/flet.h"
#include "util/freset.h"
#include "util/pair.h"
#include "util/optional.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/expr_lt.h"
#include "library/locals.h"
#include "library/num.h"
#include "library/util.h"
#include "library/norm_num.h"
#include "library/attribute_manager.h"
#include "library/defeq_canonizer.h"
#include "library/relation_manager.h"
#include "library/app_builder.h"
#include "library/congr_lemma.h"
#include "library/fun_info.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/app_builder_tactics.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/simp_lemmas_tactics.h"
#include "library/tactic/simplifier/simplifier.h"
#include "library/tactic/simplifier/theory_simplifier.h"
#include "library/tactic/simplifier/util.h"

#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_SIMPLIFY_MAX_STEPS 10000
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_NARY_ASSOC
#define LEAN_DEFAULT_SIMPLIFY_NARY_ASSOC true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_MEMOIZE
#define LEAN_DEFAULT_SIMPLIFY_MEMOIZE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL
#define LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_REWRITE
#define LEAN_DEFAULT_SIMPLIFY_REWRITE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_UNSAFE_NARY
#define LEAN_DEFAULT_SIMPLIFY_UNSAFE_NARY false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_THEORY
#define LEAN_DEFAULT_SIMPLIFY_THEORY false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_TOPDOWN
#define LEAN_DEFAULT_SIMPLIFY_TOPDOWN false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_LIFT_EQ
#define LEAN_DEFAULT_SIMPLIFY_LIFT_EQ true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_DEFEQ_CANONIZE_INSTANCES_FIXED_POINT
#define LEAN_DEFAULT_SIMPLIFY_DEFEQ_CANONIZE_INSTANCES_FIXED_POINT false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_DEFEQ_CANONIZE_PROOFS_FIXED_POINT
#define LEAN_DEFAULT_SIMPLIFY_DEFEQ_CANONIZE_PROOFS_FIXED_POINT false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_CANONIZE_SUBSINGLETONS
#define LEAN_DEFAULT_SIMPLIFY_CANONIZE_SUBSINGLETONS true
#endif

namespace lean {

static name * g_simplify_prefix = nullptr;
name get_simplify_prefix_name() { return *g_simplify_prefix; }

/* Options */

static name * g_simplify_max_steps                      = nullptr;
static name * g_simplify_nary_assoc                     = nullptr;
static name * g_simplify_memoize                        = nullptr;
static name * g_simplify_contextual                     = nullptr;
static name * g_simplify_rewrite                        = nullptr;
static name * g_simplify_unsafe_nary                    = nullptr;
static name * g_simplify_theory                         = nullptr;
static name * g_simplify_topdown                        = nullptr;
static name * g_simplify_lift_eq                        = nullptr;
static name * g_simplify_canonize_instances_fixed_point = nullptr;
static name * g_simplify_canonize_proofs_fixed_point    = nullptr;
static name * g_simplify_canonize_subsingletons         = nullptr;

name get_simplify_max_steps_name() { return *g_simplify_max_steps; }
name get_simplify_nary_assoc_name() { return *g_simplify_nary_assoc; }
name get_simplify_memoize_name() { return *g_simplify_memoize; }
name get_simplify_contextual_name() { return *g_simplify_contextual; }
name get_simplify_rewrite_name() { return *g_simplify_rewrite; }
name get_simplify_unsafe_nary_name() { return *g_simplify_unsafe_nary; }
name get_simplify_theory_name() { return *g_simplify_theory; }
name get_simplify_topdown_name() { return *g_simplify_topdown; }
name get_simplify_lift_eq_name() { return *g_simplify_lift_eq; }
name get_simplify_canonize_instances_fixed_point_name() { return *g_simplify_canonize_instances_fixed_point; }
name get_simplify_canonize_proofs_fixed_point_name() { return *g_simplify_canonize_proofs_fixed_point; }
name get_simplify_canonize_subsingletons_name() { return *g_simplify_canonize_subsingletons; }

static unsigned get_simplify_max_steps(options const & o) {
    return o.get_unsigned(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS);
}

static unsigned get_simplify_nary_assoc(options const & o) {
    return o.get_bool(*g_simplify_nary_assoc, LEAN_DEFAULT_SIMPLIFY_NARY_ASSOC);
}

static bool get_simplify_memoize(options const & o) {
    return o.get_bool(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE);
}

static bool get_simplify_contextual(options const & o) {
    return o.get_bool(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL);
}

static bool get_simplify_rewrite(options const & o) {
    return o.get_bool(*g_simplify_rewrite, LEAN_DEFAULT_SIMPLIFY_REWRITE);
}

static bool get_simplify_unsafe_nary(options const & o) {
    return o.get_bool(*g_simplify_unsafe_nary, LEAN_DEFAULT_SIMPLIFY_UNSAFE_NARY);
}

static bool get_simplify_theory(options const & o) {
    return o.get_bool(*g_simplify_theory, LEAN_DEFAULT_SIMPLIFY_THEORY);
}

static bool get_simplify_topdown(options const & o) {
    return o.get_bool(*g_simplify_topdown, LEAN_DEFAULT_SIMPLIFY_TOPDOWN);
}

static bool get_simplify_lift_eq(options const & o) {
    return o.get_bool(*g_simplify_lift_eq, LEAN_DEFAULT_SIMPLIFY_LIFT_EQ);
}

static bool get_simplify_canonize_instances_fixed_point(options const & o) {
    return o.get_bool(*g_simplify_canonize_instances_fixed_point, LEAN_DEFAULT_SIMPLIFY_DEFEQ_CANONIZE_INSTANCES_FIXED_POINT);
}

static bool get_simplify_canonize_proofs_fixed_point(options const & o) {
    return o.get_bool(*g_simplify_canonize_proofs_fixed_point, LEAN_DEFAULT_SIMPLIFY_DEFEQ_CANONIZE_PROOFS_FIXED_POINT);
}

static bool get_simplify_canonize_subsingletons(options const & o) {
    return o.get_bool(*g_simplify_canonize_subsingletons, LEAN_DEFAULT_SIMPLIFY_CANONIZE_SUBSINGLETONS);
}

#define lean_simp_trace(tctx, n, code) lean_trace(n, scope_trace_env _scope1(tctx.env(), tctx); code)

/* Main simplifier class */

class simplifier {
    type_context              m_tctx;
    theory_simplifier         m_theory_simplifier;

    name                      m_rel;

    simp_lemmas               m_slss;
    simp_lemmas               m_ctx_slss;

    optional<expr>            m_curr_nary_op;

    optional<vm_obj>          m_prove_fn;

    /* Logging */
    unsigned                  m_num_steps{0};

    bool                      m_need_restart{false};

    /* Options */
    unsigned                  m_max_steps;
    unsigned                  m_nary_assoc;
    bool                      m_memoize;
    bool                      m_contextual;
    bool                      m_rewrite;
    bool                      m_unsafe_nary;
    bool                      m_theory;
    bool                      m_topdown;
    bool                      m_lift_eq;
    bool                      m_canonize_instances_fixed_point;
    bool                      m_canonize_proofs_fixed_point;
    bool                      m_canonize_subsingletons;

    /* Cache */
    struct key {
        name              m_rel;
        expr              m_e;
        unsigned          m_hash;

        key(name const & rel, expr const & e):
            m_rel(rel), m_e(e), m_hash(hash(rel.hash(), e.hash())) { }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.m_hash; }
    };

    struct key_eq_fn {
        bool operator()(key const & k1, key const & k2) const {
            return k1.m_rel == k2.m_rel && k1.m_e == k2.m_e;
        }
    };

    typedef std::unordered_map<key, simp_result, key_hash_fn, key_eq_fn> simplify_cache;
    simplify_cache m_cache;
    optional<simp_result> cache_lookup(expr const & e);
    void cache_save(expr const & e, simp_result const & r);

    /* Basic helpers */
    environment const & env() const { return m_tctx.env(); }

    simp_result join(simp_result const & r1, simp_result const & r2) { return ::lean::join(m_tctx, m_rel, r1, r2); }

    bool using_eq() { return m_rel == get_eq_name(); }

    bool is_dependent_fn(expr const & f) {
        expr f_type = m_tctx.whnf(m_tctx.infer(f));
        lean_assert(is_pi(f_type));
        return has_free_vars(binding_body(f_type));
    }

    simp_lemmas add_to_slss(simp_lemmas const & _slss, buffer<expr> const & ls) {
        simp_lemmas slss = _slss;
        for (unsigned i = 0; i < ls.size(); i++) {
            expr const & l = ls[i];
            try {
                // TODO(Leo,Daniel): should we allow the user to set the priority of local lemmas?
                slss = add(m_tctx, slss, mlocal_name(l), m_tctx.infer(l), l, LEAN_DEFAULT_PRIORITY);
                lean_trace_d(name({"simplifier", "context"}), tout() << mlocal_name(l) << " : " << m_tctx.infer(l) << "\n";);
            } catch (exception e) {
            }
        }
        return slss;
    }

    bool should_defeq_canonize() {
        return m_canonize_instances_fixed_point || m_canonize_proofs_fixed_point;
    }

    void get_app_nary_args(expr const & op, expr const & e, buffer<expr> & nary_args) {
        if (m_unsafe_nary)
            ::lean::unsafe_get_app_nary_args(op, e, nary_args);
        else
            ::lean::get_app_nary_args(m_tctx, op, e, nary_args);
    }

    bool ops_are_the_same(expr const & op1, expr const & op2) {
        if (m_unsafe_nary)
            return get_app_fn(op1) == get_app_fn(op2);
        else
            return m_tctx.is_def_eq(op1, op2);
    }

    bool instantiate_emetas(tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas, list<bool> const & instances);

    /* Simp_Results */
    simp_result lift_from_eq(expr const & old_e, simp_result const & r_eq);

    /* Main simplify method */
    simp_result simplify(expr const & old_e) {
        m_num_steps++;
        lean_trace_inc_depth("simplifier");
        lean_trace_d("simplifier", tout() << m_rel << ": " << old_e << "\n";);

        if (m_num_steps > m_max_steps) {
            lean_trace(name({"simplifier", "failed"}), tout() << m_rel << ": " << old_e << "\n";);
            throw exception("simplifier failed, maximum number of steps exceeded");
        }

        if (m_memoize) {
            if (auto it = cache_lookup(old_e))
                return *it;
        }

        expr e = whnf_eta(old_e);
        simp_result r;

        optional<pair<expr, expr> > assoc;
        if (m_nary_assoc && using_eq())
            assoc = is_assoc(m_tctx, e);

        if (assoc) {
            bool use_congr_only = assoc && m_curr_nary_op && *m_curr_nary_op == assoc->second;
            flet<optional<expr> > in_nary_subtree(m_curr_nary_op, some_expr(assoc->second));
            r = simplify_nary(assoc->first, assoc->second, e, use_congr_only);
        } else {
            flet<optional<expr> > not_in_nary_subtree(m_curr_nary_op, none_expr());
            r = simplify_binary(e);
        }

        if (!r.is_done())
            r = join(r, simplify(r.get_new()));

        if (m_lift_eq && !using_eq()) {
            simp_result r_eq;
            {
                flet<name> use_eq(m_rel, get_eq_name());
                r_eq = simplify(r.get_new());
            }
            if (r_eq.get_new() != r.get_new()) {
                r = join(r, lift_from_eq(r.get_new(), r_eq));
                r = join(r, simplify(r.get_new()));
            }
        }

        if (m_memoize)
            cache_save(old_e, r);

        return r;
    }

    simp_result simplify_rewrite_binary(expr const & e) {
        simp_lemmas slss = ::lean::join(m_slss, m_ctx_slss);
        simp_lemmas_for const * sr = slss.find(m_rel);
        if (!sr) return simp_result(e);

        list<simp_lemma> const * srs = sr->find(e);
        if (!srs) {
            lean_trace_d(name({"debug", "simplifier", "try_rewrite"}), tout() << "no simp lemmas for: " << e << "\n";);
            return simp_result(e);
        }

        for (simp_lemma const & lemma : *srs) {
            simp_result r = rewrite_binary(e, lemma);
            if (!is_eqp(r.get_new(), e)) {
                lean_trace_d(name({"simplifier", "rewrite"}), tout() << "[" << lemma.get_id() << "]: " << e << " ==> " << r.get_new() << "\n";);
                return r;
            }
        }
        return simp_result(e);
    }

    simp_result rewrite_binary(expr const & e, simp_lemma const & sl) {
        tmp_type_context tmp_tctx(m_tctx, sl.get_num_umeta(), sl.get_num_emeta());
        if (!tmp_tctx.is_def_eq(e, sl.get_lhs())) {
            lean_trace_d(name({"debug", "simplifier", "try_rewrite"}), tout() << "fail to unify: " << sl.get_id() << "\n";);
            return simp_result(e);
        }
        if (!instantiate_emetas(tmp_tctx, sl.get_num_emeta(), sl.get_emetas(), sl.get_instances())) {
            lean_trace_d(name({"debug", "simplifier", "try_rewrite"}), tout() << "fail to instantiate emetas: " << sl.get_id() << "\n";);
            return simp_result(e);
        }

        for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
            if (!tmp_tctx.is_uassigned(i))
                return simp_result(e);
        }

        expr new_lhs = tmp_tctx.instantiate_mvars(sl.get_lhs());
        expr new_rhs = tmp_tctx.instantiate_mvars(sl.get_rhs());
        if (sl.is_permutation()) {
            if (!is_lt(new_rhs, new_lhs, false)) {
                lean_simp_trace(tmp_tctx, name({"simplifier", "perm"}),
                                tout() << "perm rejected: " << new_rhs << " !< " << new_lhs << "\n";);
                return simp_result(e);
            }
        }

        if (sl.is_refl()) {
            return simp_result(new_rhs);
        } else {
            expr pf = tmp_tctx.instantiate_mvars(sl.get_proof());
            return simp_result(new_rhs, pf);
        }
    }

    simp_result simplify_subterms_app_binary(expr const & _e) {
        lean_assert(is_app(_e));
        expr e = should_defeq_canonize() ? defeq_canonize_args_step(_e) : _e;

        // (1) Try user-defined congruences
        simp_result r_user = try_congrs(e);
        if (r_user.has_proof()) {
            if (using_eq()) {
                return join(r_user, simplify_operator_of_app(r_user.get_new()));
            } else {
                return r_user;
            }
        }

        // (2) Synthesize congruence lemma
        if (using_eq()) {
            optional<simp_result> r_args = synth_congr(e);
            if (r_args) return join(*r_args, simplify_operator_of_app(r_args->get_new()));
        }
        // (3) Fall back on generic binary congruence
        if (using_eq()) {
            expr const & f = app_fn(e);
            expr const & arg = app_arg(e);

            simp_result r_f = simplify(f);

            if (is_dependent_fn(f)) {
                if (r_f.has_proof()) return congr_fun(r_f, arg);
                else return mk_app(r_f.get_new(), arg);
            } else {
                simp_result r_arg = simplify(arg);
                return congr_fun_arg(r_f, r_arg);
            }
        }
        return simp_result(e);
    }


    // Main binary simplify method
    simp_result simplify_binary(expr const & e) {
        if (m_topdown) {
            if (m_rewrite) {
                simp_result r_rewrite = simplify_rewrite_binary(e);
                if (r_rewrite.get_new() != e) {
                    return r_rewrite;
                }
            }
        }

        // [1] Simplify subterms using congruence
        simp_result r(e);

        if (!using_eq() || !m_theory_simplifier.owns(e)) {
            switch (r.get_new().kind()) {
            case expr_kind::Local:
            case expr_kind::Meta:
            case expr_kind::Sort:
            case expr_kind::Constant:
            case expr_kind::Macro:
                // no-op
                break;
            case expr_kind::Lambda:
                if (using_eq())
                    r = simplify_subterms_lambda(r.get_new());
                break;
            case expr_kind::Pi:
                r = simplify_subterms_pi(r.get_new());
                break;
            case expr_kind::App:
                r = simplify_subterms_app_binary(r.get_new());
                break;
            case expr_kind::Let:
                // whnf unfolds let-expressions
                // TODO(dhs, leo): add flag for type_context not to unfold let-expressions
                lean_unreachable();
            case expr_kind::Var:
                lean_unreachable();
            }

            if (r.get_new() != e) {
                lean_trace_d(name({"simplifier", "congruence"}), tout() << e << " ==> " << r.get_new() << "\n";);
                if (m_topdown)
                    return r;
            }
        }

        if (!m_topdown) {
            if (m_rewrite) {
                simp_result r_rewrite = simplify_rewrite_binary(r.get_new());
                if (r_rewrite.get_new() != r.get_new()) {
                    lean_trace_d(name({"simplifier", "rewrite"}), tout() << r.get_new() << " ==> " << r_rewrite.get_new() << "\n";);
                    return join(r, r_rewrite);
                }
            }
        }

        // [5] Simplify with the theory simplifier
        // Note: the theory simplifier guarantees that no new subterms are introduced that need to be simplified.
        // Thus we never need to repeat unless something is simplified downstream of here.
        if (using_eq() && m_theory) {
            simp_result r_theory = m_theory_simplifier.simplify_binary(r.get_new());
            if (r_theory.get_new() != r.get_new()) {
                lean_trace_d(name({"simplifier", "theory"}), tout() << r.get_new() << " ==> " << r_theory.get_new() << "\n";);
                r = join(r, r_theory);
            }
        }

        r.set_done();
        return r;
    }

    // n-ary methods
    optional<simp_result> simplify_rewrite_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> const & nary_args) {
        simp_lemmas slss = ::lean::join(m_slss, m_ctx_slss);
        simp_lemmas_for const * sr = slss.find(m_rel);
        if (!sr)
            return optional<simp_result>();

        list<simp_lemma> const * srs = sr->find(op);
        if (!srs) {
            return optional<simp_result>();
        }

        for (simp_lemma const & lemma : *srs) {
            if (optional<simp_result> r = rewrite_nary(assoc, old_e, op, nary_args, lemma))
                return r;
        }
        return optional<simp_result>();
    }

    optional<simp_result> rewrite_nary(expr const & assoc, expr const & old_e, expr const & op, buffer<expr> const & nary_args, simp_lemma const & sl) {
        optional<expr> pattern_op = get_binary_op(sl.get_lhs());
        if (!pattern_op)
            return optional<simp_result>();

        tmp_type_context tmp_tctx(m_tctx, sl.get_num_umeta(), sl.get_num_emeta());
        if (!tmp_tctx.is_def_eq(op, *pattern_op))
            return optional<simp_result>();

        buffer<expr> nary_pattern_args;
        get_app_nary_args(*pattern_op, sl.get_lhs(), nary_pattern_args);

        unsigned num_patterns = nary_pattern_args.size();

        if (nary_args.size() < num_patterns)
            return optional<simp_result>();

        // TODO(dhs): return an n-ary macro, and have simplify(e) unfold these at the end
        // Reason: multiple rewrites and theory steps could avoid reconstructing the term
        // Reason for postponing: easy to support and may not be a bottleneck
        for (unsigned i = 0; i <= nary_args.size() - num_patterns; ++i) {
            if (optional<simp_result> r = rewrite_nary_step(nary_args, nary_pattern_args, i, sl)) {
                // lean_assert(r->has_proof());
                unsigned j = nary_args.size() - 1;
                expr new_e = (j >= i + num_patterns) ? nary_args[j] : r->get_new();
                j = (j >= i + num_patterns) ? (j - 1) : (j - num_patterns);
                while (j + 1 > 0) {
                    if (j >= i + num_patterns || j < i) {
                        new_e = mk_app(op, nary_args[j], new_e);
                        j -= 1;
                    } else {
                        new_e = mk_app(op, r->get_new(), new_e);
                        j -= num_patterns;
                    }
                }
                return optional<simp_result>(simp_result(new_e, mk_rewrite_assoc_proof(assoc, mk_eq(m_tctx, old_e, new_e),
                                                                                       i, num_patterns, nary_args.size(), r->get_new(), r->get_proof())));
            }
        }
        return optional<simp_result>();
    }

    optional<simp_result> rewrite_nary_step(buffer<expr> const & nary_args, buffer<expr> const & nary_pattern_args, unsigned offset, simp_lemma const & sl) {
        tmp_type_context tmp_tctx(m_tctx, sl.get_num_umeta(), sl.get_num_emeta());
        for (unsigned i = 0; i < nary_pattern_args.size(); ++i) {
            if (!tmp_tctx.is_def_eq(nary_args[offset+i], nary_pattern_args[i]))
                return optional<simp_result>();
        }

        if (!instantiate_emetas(tmp_tctx, sl.get_num_emeta(), sl.get_emetas(), sl.get_instances()))
            return optional<simp_result>();

        for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
            if (!tmp_tctx.is_uassigned(i))
                return optional<simp_result>();
        }

        expr new_lhs = tmp_tctx.instantiate_mvars(sl.get_lhs());
        expr new_rhs = tmp_tctx.instantiate_mvars(sl.get_rhs());

        if (sl.is_permutation()) {
            if (!is_lt(new_rhs, new_lhs, false)) {
                lean_simp_trace(tmp_tctx, name({"simplifier", "perm"}),
                                tout() << "perm rejected: " << new_rhs << " !< " << new_lhs << "\n";);
                return optional<simp_result>();
            }
        }
        if (sl.is_refl()) {
            return optional<simp_result>(simp_result(new_rhs));
        } else {
            expr pf = tmp_tctx.instantiate_mvars(sl.get_proof());
            return optional<simp_result>(simp_result(new_rhs, pf));
        }
    }

    simp_result simplify_subterms_app_nary_core(expr const & old_op, expr const & new_op, optional<expr> const & pf_op, expr const & e) {
        expr arg1, arg2;
        optional<expr> op = get_binary_op(e, arg1, arg2);
        if (op && ops_are_the_same(*op, old_op)) {
            simp_result r(e);
            if (pf_op)
                r = join(r, simp_result(mk_app(new_op, arg1, arg2), mk_congr_bin_op(m_tctx, *pf_op, arg1, arg2)));

            simp_result r1 = simplify_subterms_app_nary_core(old_op, new_op, pf_op, arg1);
            simp_result r2 = simplify_subterms_app_nary_core(old_op, new_op, pf_op, arg2);

            expr new_e = mk_app(new_op, r1.get_new(), r2.get_new());
            if (r1.has_proof() && r2.has_proof()) {
                return join(r, simp_result(new_e, mk_congr_bin_args(m_tctx, new_op, r1.get_proof(), r2.get_proof())));
            } else if (r1.has_proof()) {
                return join(r, simp_result(new_e, mk_congr_bin_arg1(m_tctx, new_op, r1.get_proof(), r2.get_new())));
            } else if (r2.has_proof()) {
                return join(r, simp_result(new_e, mk_congr_bin_arg2(m_tctx, new_op, r1.get_new(), r2.get_proof())));
            } else {
                r.update(new_e);
                return r;
            }
        } else {
            return simplify(e);
        }
    }

    simp_result simplify_subterms_app_nary(expr const & old_op, expr const & e) {
        simp_result pf_op = simplify(old_op);
        return simplify_subterms_app_nary_core(old_op, old_op, pf_op.get_optional_proof(), e);
    }

    // Main n-ary simplify method
    simp_result simplify_nary(expr const & assoc, expr const & op, expr const & old_e, bool use_congr_only) {
        lean_assert(using_eq());

        if (m_topdown && !use_congr_only) {
            buffer<expr> nary_args;
            get_app_nary_args(op, old_e, nary_args);

            expr flat_e = mk_nary_app(op, nary_args);
            simp_result r_flat(flat_e, mk_flat_proof(assoc, mk_eq(m_tctx, old_e, flat_e)));

            if (m_rewrite) {
                if (optional<simp_result> r_rewrite = simplify_rewrite_nary(assoc, r_flat.get_new(), op, nary_args)) {
                    lean_trace_d(name({"simplifier", "rewrite"}), tout() << old_e << " ==> " << r_rewrite->get_new() << "\n";);
                    return join(r_flat, *r_rewrite);
                }
            }
        }

        simp_result r_congr = simplify_subterms_app_nary(op, old_e);
        expr new_op = *get_binary_op(r_congr.get_new());

        buffer<expr> new_nary_args;
        get_app_nary_args(new_op, r_congr.get_new(), new_nary_args);
        expr congr_flat_e = mk_nary_app(new_op, new_nary_args);
        simp_result r_congr_flat = join(r_congr, simp_result(congr_flat_e, mk_flat_proof(assoc, mk_eq(m_tctx, r_congr.get_new(), congr_flat_e))));

        if (m_topdown && r_congr_flat.get_new() != old_e)
            return r_congr_flat;

        if (!m_topdown && !use_congr_only) {
            if (m_rewrite) {
                if (optional<simp_result> r_rewrite = simplify_rewrite_nary(assoc, r_congr_flat.get_new(), new_op, new_nary_args)) {
                    lean_trace_d(name({"simplifier", "rewrite"}), tout() << old_e << " ==> " << r_rewrite->get_new() << "\n";);
                    return join(r_congr_flat, *r_rewrite);
                }
            }
        }

        // [5] Simplify with the theory simplifier
        // Note: the theory simplifier guarantees that no new subterms are introduced that need to be simplified.
        // Thus we never need to repeat unless something is simplified downstream of here.
        if (m_theory && !use_congr_only) {
            if (optional<simp_result> r_theory = m_theory_simplifier.simplify_nary(assoc, r_congr_flat.get_new(), new_op, new_nary_args)) {
                lean_trace_d(name({"simplifier", "theory"}), tout() << old_e << " ==> " << r_theory->get_new() << "\n";);
                simp_result r = join(r_congr_flat, *r_theory);
                r.set_done();
                return r;
            }
        }

        r_congr_flat.set_done();
        return r_congr_flat;
    }

    /* Simplifying the necessary subterms */
    simp_result simplify_subterms_lambda(expr const & e);
    simp_result simplify_subterms_pi(expr const & e);
    simp_result simplify_subterms_app(expr const & e);

    /* Called from simplify_subterms_app */
    simp_result simplify_operator_of_app(expr const & e);

    /* Proving */
    optional<expr> prove(expr const & thm);

    /* Canonicalize */
    expr defeq_canonize_args_step(expr const & e);

    expr_struct_map<expr> m_subsingleton_elem_map;
    simp_result canonize_subsingleton_args(expr const & e);

    /* Congruence */
    simp_result congr_fun_arg(simp_result const & r_f, simp_result const & r_arg);
    simp_result congr(simp_result const & r_f, simp_result const & r_arg);
    simp_result congr_fun(simp_result const & r_f, expr const & arg);
    simp_result congr_arg(expr const & f, simp_result const & r_arg);
    simp_result congr_funs(simp_result const & r_f, buffer<expr> const & args);
    simp_result funext(simp_result const & r, expr const & l);

    simp_result try_congrs(expr const & e);
    simp_result try_congr(expr const & e, simp_lemma const & cr);

    optional<simp_result> synth_congr(expr const & e);

    expr remove_unnecessary_casts(expr const & e);

    /* Apply whnf and eta-reduction
       \remark We want (Sum n (fun x, f x)) and (Sum n f) to be the same.
       \remark We may want to switch to eta-expansion later (see paper: "The Virtues of Eta-expansion").
       TODO(Daniel, Leo): should we add an option for disabling/enabling eta? */
    expr whnf_eta(expr const & e);

public:
    simplifier(type_context & tctx, name const & rel, simp_lemmas const & slss, optional<vm_obj> const & prove_fn):
        m_tctx(tctx), m_theory_simplifier(tctx), m_rel(rel), m_slss(slss), m_prove_fn(prove_fn),
        /* Options */
        m_max_steps(get_simplify_max_steps(tctx.get_options())),
        m_nary_assoc(get_simplify_nary_assoc(tctx.get_options())),
        m_memoize(get_simplify_memoize(tctx.get_options())),
        m_contextual(get_simplify_contextual(tctx.get_options())),
        m_rewrite(get_simplify_rewrite(tctx.get_options())),
        m_unsafe_nary(get_simplify_unsafe_nary(tctx.get_options())),
        m_theory(get_simplify_theory(tctx.get_options())),
        m_topdown(get_simplify_topdown(tctx.get_options())),
        m_lift_eq(get_simplify_lift_eq(tctx.get_options())),
        m_canonize_instances_fixed_point(get_simplify_canonize_instances_fixed_point(tctx.get_options())),
        m_canonize_proofs_fixed_point(get_simplify_canonize_proofs_fixed_point(tctx.get_options())),
        m_canonize_subsingletons(get_simplify_canonize_subsingletons(tctx.get_options()))
        { }

    simp_result operator()(expr const & e)  {
        scope_trace_env scope(env(), m_tctx.get_options(), m_tctx);
        simp_result r(e);
        while (true) {
            m_need_restart = false;
            r = join(r, simplify(r.get_new()));
            if (!m_need_restart || !should_defeq_canonize())
                return r;
            m_cache.clear();
        }
        return simplify(e);
    }
};

/* Cache */

optional<simp_result> simplifier::cache_lookup(expr const & e) {
    auto it = m_cache.find(key(m_rel, e));
    if (it == m_cache.end()) return optional<simp_result>();
    return optional<simp_result>(it->second);
}

void simplifier::cache_save(expr const & e, simp_result const & r) {
    m_cache.insert(mk_pair(key(m_rel, e), r));
}

/* Simp_Results */

simp_result simplifier::lift_from_eq(expr const & old_e, simp_result const & r_eq) {
    if (!r_eq.has_proof()) return r_eq;
    lean_assert(r_eq.has_proof());
    /* r_eq.get_proof() : old_e = r_eq.get_new() */
    /* goal : old_e <m_rel> r_eq.get_new() */
    type_context::tmp_locals local_factory(m_tctx);
    expr local = local_factory.push_local(name(), m_tctx.infer(old_e));
    expr motive_local = mk_app(m_tctx, m_rel, old_e, local);
    /* motive = fun y, old_e <m_rel> y */
    expr motive = local_factory.mk_lambda(motive_local);
    /* Rxx = x <m_rel> x */
    expr Rxx = mk_refl(m_tctx, m_rel, old_e);
    expr pf = mk_eq_rec(m_tctx, motive, Rxx, r_eq.get_proof());
    return simp_result(r_eq.get_new(), pf);
}

/* Whnf + Eta */
expr simplifier::whnf_eta(expr const & e) {
    return try_eta(m_tctx.whnf(e));
}

simp_result simplifier::simplify_subterms_lambda(expr const & old_e) {
    lean_assert(is_lambda(old_e));
    expr e = old_e;

    buffer<expr> ls;
    while (is_lambda(e)) {
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = m_tctx.push_local(binding_name(e), d, binding_info(e));
        ls.push_back(l);
        e = instantiate(binding_body(e), l);
    }

    simp_result r = simplify(e);
    expr new_e = r.get_new();
    expr new_e_type = m_tctx.infer(new_e);
    if (auto inst = m_tctx.mk_subsingleton_instance(new_e_type)) {
        auto it = m_subsingleton_elem_map.find(new_e_type);
        if (it != m_subsingleton_elem_map.end()) {
            // We do not canonize when there is an unfavourable locals mismatch
            // TODO(dhs): maintain a list of canonical elements as we do in the defeq-canonizer
            if (it->second != new_e && locals_subset(it->second, new_e)) {
                expr proof = mk_ss_elim(m_tctx, new_e_type, *inst, new_e, it->second);
                r = join(r, simp_result(it->second, proof));
                lean_trace_d(name({"simplifier", "subsingleton"}), tout() << new_e << " ==> " << it->second << "\n";);
            }
        } else {
            m_subsingleton_elem_map.insert(mk_pair(new_e_type, new_e));
        }
    }

    if (r.get_new() == e)
        return old_e;

    if (!r.has_proof())
        return m_tctx.mk_lambda(ls, r.get_new());

    for (int i = ls.size() - 1; i >= 0; --i)
        r = funext(r, ls[i]);

    return r;
}

simp_result simplifier::simplify_subterms_pi(expr const & e) {
    lean_assert(is_pi(e));
    return try_congrs(e);
}

expr simplifier::defeq_canonize_args_step(expr const & e) {
    buffer<expr> args;
    bool modified = false;
    expr f        = get_app_args(e, args);
    fun_info info = get_fun_info(m_tctx, f, args.size());
    unsigned i    = 0;
    for (param_info const & pinfo : info.get_params_info()) {
        lean_assert(i < args.size());
        expr new_a;
        if ((m_canonize_instances_fixed_point && pinfo.is_inst_implicit()) || (m_canonize_proofs_fixed_point && pinfo.is_prop())) {
            new_a = ::lean::defeq_canonize(m_tctx, args[i], m_need_restart);
            lean_trace(name({"simplifier", "canonize"}),
                       tout() << "\n" << args[i] << "\n==>\n" << new_a << "\n";);
            if (new_a != args[i]) {
                modified = true;
                args[i] = new_a;
            }
        }
        i++;
    }

    if (!modified)
        return e;
    else
        return mk_app(f, args);
}

simp_result simplifier::simplify_operator_of_app(expr const & e) {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    simp_result r_f = simplify(f);
    return congr_funs(r_f, args);
}

/* Proving */
optional<expr> simplifier::prove(expr const & goal) {
    if (!m_prove_fn)
        return none_expr();

    metavar_context mctx = m_tctx.mctx();
    expr goal_mvar = mctx.mk_metavar_decl(m_tctx.lctx(), goal);
    lean_trace(name({"simplifier", "prove"}), tout() << "goal: " << goal_mvar << " : " << goal << "\n";);
    vm_obj s = to_obj(tactic_state(m_tctx.env(), m_tctx.get_options(), mctx, list<expr>(goal_mvar), goal_mvar));
    vm_obj prove_fn_result = invoke(*m_prove_fn, s);
    optional<tactic_state> s_new = is_tactic_success(prove_fn_result);
    if (s_new) {
        if (!s_new->mctx().is_assigned(goal_mvar)) {
            lean_trace(name({"simplifier", "prove"}), tout() << "prove_fn succeeded but did not return a proof\n";);
            return none_expr();
        }
        metavar_context smctx = s_new->mctx();
        expr proof = smctx.instantiate_mvars(goal_mvar);
        optional<expr> new_metavar = find(proof, [&](expr const & e, unsigned) {
                return is_metavar(e) && !static_cast<bool>(m_tctx.mctx().get_metavar_decl(e));
            });
        if (new_metavar) {
            lean_trace(name({"simplifier", "prove"}),
                       tout() << "prove_fn succeeded but left an unrecognized metavariable of type "
                       << smctx.get_metavar_decl(*new_metavar)->get_type() << " in proof\n";);
            return none_expr();
        }
        m_tctx.set_mctx(s_new->mctx());
        lean_trace(name({"simplifier", "prove"}), tout() << "success: " << proof << " : " << m_tctx.infer(proof) << "\n";);
        return some_expr(proof);
    } else {
        lean_trace(name({"simplifier", "prove"}), tout() << "prove_fn failed to prove " << goal << "\n";);
        return none_expr();
    }
}

/* Congruence */

simp_result simplifier::congr_fun_arg(simp_result const & r_f, simp_result const & r_arg) {
    if (!r_f.has_proof() && !r_arg.has_proof()) return simp_result(mk_app(r_f.get_new(), r_arg.get_new()));
    else if (!r_f.has_proof()) return congr_arg(r_f.get_new(), r_arg);
    else if (!r_arg.has_proof()) return congr_fun(r_f, r_arg.get_new());
    else return congr(r_f, r_arg);
}

simp_result simplifier::congr(simp_result const & r_f, simp_result const & r_arg) {
    lean_assert(r_f.has_proof() && r_arg.has_proof());
    // theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
    expr e  = mk_app(r_f.get_new(), r_arg.get_new());
    expr pf = mk_congr(m_tctx, r_f.get_proof(), r_arg.get_proof());
    return simp_result(e, pf);
}

simp_result simplifier::congr_fun(simp_result const & r_f, expr const & arg) {
    lean_assert(r_f.has_proof());
    // theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
    expr e  = mk_app(r_f.get_new(), arg);
    expr pf = mk_congr_fun(m_tctx, r_f.get_proof(), arg);
    return simp_result(e, pf);
}

simp_result simplifier::congr_arg(expr const & f, simp_result const & r_arg) {
    lean_assert(r_arg.has_proof());
    // theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂
    expr e  = mk_app(f, r_arg.get_new());
    expr pf = mk_congr_arg(m_tctx, f, r_arg.get_proof());
    return simp_result(e, pf);
}

/* Note: handles reflexivity */
simp_result simplifier::congr_funs(simp_result const & r_f, buffer<expr> const & args) {
    expr e = r_f.get_new();
    for (unsigned i = 0; i < args.size(); ++i) {
        e  = mk_app(e, args[i]);
    }
    if (!r_f.has_proof())
        return simp_result(e);
    expr pf = r_f.get_proof();
    for (unsigned i = 0; i < args.size(); ++i) {
        pf = mk_congr_fun(m_tctx, pf, args[i]);
    }
    return simp_result(e, pf);
}

simp_result simplifier::funext(simp_result const & r, expr const & l) {
    expr e = m_tctx.mk_lambda(l, r.get_new());
    if (!r.has_proof())
        return simp_result(e);
    expr lam_pf = m_tctx.mk_lambda(l, r.get_proof());
    expr pf = mk_funext(m_tctx, lam_pf);
    return simp_result(e, pf);
}

simp_result simplifier::try_congrs(expr const & e) {
    simp_lemmas_for const * sls = m_slss.find(m_rel);
    if (!sls) return simp_result(e);

    list<simp_lemma> const * cls = sls->find_congr(e);
    if (!cls) return simp_result(e);

    for (simp_lemma const & cl : *cls) {
        simp_result r = try_congr(e, cl);
        if (r.get_new() != e)
            return r;
    }
    return simp_result(e);
}

simp_result simplifier::try_congr(expr const & e, simp_lemma const & cl) {
    tmp_type_context tmp_tctx(m_tctx, cl.get_num_umeta(), cl.get_num_emeta());
    if (!tmp_tctx.is_def_eq(e, cl.get_lhs()))
        return simp_result(e);

    lean_simp_trace(tmp_tctx, name({"debug", "simplifier", "try_congruence"}),
                    tout() << "(" << cl.get_id() << ") " << e << "\n";);

    bool simplified = false;

    buffer<expr> congr_hyps;
    to_buffer(cl.get_congr_hyps(), congr_hyps);

    buffer<simp_result> congr_hyp_results;
    buffer<type_context::tmp_locals> factories;
    buffer<name> relations;
    for (expr const & m : congr_hyps) {
        factories.emplace_back(m_tctx);
        type_context::tmp_locals & local_factory = factories.back();
        expr m_type = tmp_tctx.instantiate_mvars(tmp_tctx.infer(m));

        while (is_pi(m_type)) {
            expr d = instantiate_rev(binding_domain(m_type), local_factory.as_buffer().size(), local_factory.as_buffer().data());
            expr l = local_factory.push_local(binding_name(m_type), d, binding_info(m_type));
            lean_assert(!has_metavar(l));
            m_type = binding_body(m_type);
        }
        m_type = instantiate_rev(m_type, local_factory.as_buffer().size(), local_factory.as_buffer().data());

        expr h_rel, h_lhs, h_rhs;
        lean_verify(is_simp_relation(tmp_tctx.env(), m_type, h_rel, h_lhs, h_rhs) && is_constant(h_rel));
        {
            flet<name> set_name(m_rel, const_name(h_rel));
            relations.push_back(m_rel);
            flet<simp_lemmas> set_ctx_slss(m_ctx_slss, m_contextual ? add_to_slss(m_ctx_slss, local_factory.as_buffer()) : m_ctx_slss);

            h_lhs = tmp_tctx.instantiate_mvars(h_lhs);
            /* TODO(Leo, Daniel): the original assertion was !has_metavar(h_lhs).
               It is incorrect. I got an assertion violation when processing
               a term containing universe meta-variables. So, I relaxed it to !has_expr_metavar(h_lhs).
               We should investigate this. Example: what happens if the input expression has
               regular meta-variables? Perhaps, the right assertion is: h_lhs does *not* have temporary
               universe and regular meta-variables. */
            lean_assert(!has_expr_metavar(h_lhs));

            if (m_contextual) {
                freset<simplify_cache> reset_cache(m_cache);
                congr_hyp_results.emplace_back(simplify(h_lhs));
            } else {
                congr_hyp_results.emplace_back(simplify(h_lhs));
            }
            simp_result const & r_congr_hyp = congr_hyp_results.back();

            if (r_congr_hyp.has_proof())
                simplified = true;

            lean_assert(is_meta(h_rhs));
            buffer<expr> new_val_meta_args;
            expr new_val_meta = get_app_args(h_rhs, new_val_meta_args);
            lean_assert(is_metavar(new_val_meta));
            expr new_val = tmp_tctx.mk_lambda(new_val_meta_args, r_congr_hyp.get_new());
            tmp_tctx.assign(new_val_meta, new_val);
        }
    }

    if (!simplified)
        return simp_result(e);

    lean_assert(congr_hyps.size() == congr_hyp_results.size());
    for (unsigned i = 0; i < congr_hyps.size(); ++i) {
        expr const & pf_meta = congr_hyps[i];
        simp_result const & r_congr_hyp = congr_hyp_results[i];
        name const & rel = relations[i];
        type_context::tmp_locals & local_factory = factories[i];
        expr hyp = finalize(m_tctx, rel, r_congr_hyp).get_proof();
        // This is the current bottleneck
        // Can address somewhat by keeping the proofs as small as possible using macros
        expr pf = local_factory.mk_lambda(hyp);
        tmp_tctx.assign(pf_meta, pf);
    }

    if (!instantiate_emetas(tmp_tctx, cl.get_num_emeta(), cl.get_emetas(), cl.get_instances()))
        return simp_result(e);

    for (unsigned i = 0; i < cl.get_num_umeta(); i++) {
        if (!tmp_tctx.is_uassigned(i))
            return simp_result(e);
    }

    expr e_s = tmp_tctx.instantiate_mvars(cl.get_rhs());
    expr pf = tmp_tctx.instantiate_mvars(cl.get_proof());

    simp_result r(e_s, pf);
    if (is_app(e_s))
        r = join(r, canonize_subsingleton_args(r.get_new()));

    lean_simp_trace(tmp_tctx, name({"simplifier", "congruence"}),
                    tout() << "(" << cl.get_id() << ") "
                    << "[" << e << " ==> " << e_s << "]\n";);

    return r;
}

bool simplifier::instantiate_emetas(tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas, list<bool> const & instances) {
    bool failed = false;
    unsigned i = num_emeta;
    for_each2(emetas, instances, [&](expr const & m, bool const & is_instance) {
            i--;
            if (failed) return;
            expr m_type = tmp_tctx.instantiate_mvars(tmp_tctx.infer(m));
            if (has_metavar(m_type)) {
                failed = true;
                return;
            }

            if (tmp_tctx.is_eassigned(i)) return;

            if (is_instance) {
                if (auto v = m_tctx.mk_class_instance(m_type)) {
                    if (!tmp_tctx.is_def_eq(m, *v)) {
                        lean_simp_trace(tmp_tctx, name({"simplifier", "failure"}),
                                        tout() << "unable to assign instance for: " << m_type << "\n";);
                        failed = true;
                        return;
                    }
                } else {
                    lean_simp_trace(tmp_tctx, name({"simplifier", "failure"}),
                                    tout() << "unable to synthesize instance for: " << m_type << "\n";);
                    failed = true;
                    return;
                }
            }

            if (tmp_tctx.is_eassigned(i)) return;

            // Note: m_type has no metavars
            if (m_tctx.is_prop(m_type)) {
                if (auto pf = prove(m_type)) {
                    lean_verify(tmp_tctx.is_def_eq(m, *pf));
                    return;
                }
            }

            lean_simp_trace(tmp_tctx, name({"simplifier", "failure"}),
                            tout() << "failed to assign: " << m << " : " << m_type << "\n";);

            failed = true;
            return;
        });

    return !failed;
}

optional<simp_result> simplifier::synth_congr(expr const & e) {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    auto congr_lemma = mk_specialized_congr_simp(m_tctx, e);
    if (!congr_lemma) return optional<simp_result>();

    buffer<simp_result> r_args;
    buffer<expr>        new_args;
    bool has_proof = false;
    bool has_cast = false;
    bool has_simplified = false;

    unsigned i = 0;

    // First pass, try to simplify all the Eq arguments
    for (congr_arg_kind const & ckind : congr_lemma->get_arg_kinds()) {
        switch (ckind) {
        case congr_arg_kind::HEq:
            lean_unreachable();
        case congr_arg_kind::Fixed:
        case congr_arg_kind::FixedNoParam:
            new_args.emplace_back(args[i]);
            break;
        case congr_arg_kind::Eq:
            {
                r_args.emplace_back(simplify(args[i]));
                simp_result & r_arg = r_args.back();
                new_args.emplace_back(r_arg.get_new());
                if (r_arg.has_proof())
                    has_proof = true;
                if (r_arg.get_new() != args[i])
                    has_simplified = true;
            }
            break;
        case congr_arg_kind::Cast:
            has_cast = true;
            new_args.emplace_back(args[i]);
            break;
        }
        i++;
    }

    if (!has_simplified) {
        simp_result r = simp_result(e);
        if (has_cast)
            r = join(r, canonize_subsingleton_args(r.get_new()));
        return optional<simp_result>(r);
    }

    if (!has_proof) {
        simp_result r = simp_result(mk_app(f, new_args));
        if (has_cast)
            r = join(r, canonize_subsingleton_args(r.get_new()));
        return optional<simp_result>(r);
    }

    // We have a proof, so we need to build the congruence lemma
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    buffer<expr> subst;

    i = 0;
    unsigned i_eq = 0;
    for (congr_arg_kind const & ckind : congr_lemma->get_arg_kinds()) {
        switch (ckind) {
        case congr_arg_kind::HEq:
            lean_unreachable();
        case congr_arg_kind::Fixed:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            break;
        case congr_arg_kind::FixedNoParam:
            break;
        case congr_arg_kind::Eq:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            {
                simp_result r_arg = finalize(m_tctx, m_rel, r_args[i_eq]);
                proof = mk_app(proof, r_arg.get_new(), r_arg.get_proof());
                subst.push_back(r_arg.get_new());
                subst.push_back(r_arg.get_proof());
            }
            type = binding_body(binding_body(type));
            i_eq++;
            break;
        case congr_arg_kind::Cast:
            lean_assert(has_cast);
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            break;
        }
        i++;
    }
    lean_assert(is_eq(type));
    expr rhs   = instantiate_rev(app_arg(type), subst.size(), subst.data());
    simp_result r(rhs, proof);

    if (has_cast) {
        r.update(remove_unnecessary_casts(r.get_new()));
        r = join(r, canonize_subsingleton_args(r.get_new()));
    }

    return optional<simp_result>(r);
}

// Given a function application \c e, replace arguments that are subsingletons with a
// representative
simp_result simplifier::canonize_subsingleton_args(expr const & e) {
    // TODO(dhs): flag to skip this step
    buffer<expr> args;
    get_app_args(e, args);
    auto congr_lemma = mk_specialized_congr(m_tctx, e);
    if (!congr_lemma)
        return simp_result(e);
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    unsigned i = 0;
    bool modified = false;
    for_each(congr_lemma->get_arg_kinds(), [&](congr_arg_kind const & ckind) {
            expr rfl;
            switch (ckind) {
            case congr_arg_kind::HEq:
                lean_unreachable();
            case congr_arg_kind::Fixed:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                break;
            case congr_arg_kind::FixedNoParam:
                break;
            case congr_arg_kind::Eq:
                proof = mk_app(proof, args[i]);
                type = instantiate(binding_body(type), args[i]);
                rfl = mk_eq_refl(m_tctx, args[i]);
                proof = mk_app(proof, args[i], rfl);
                type = instantiate(binding_body(type), args[i]);
                type = instantiate(binding_body(type), rfl);
                break;
            case congr_arg_kind::Cast:
                proof = mk_app(proof, args[i]);
                type  = instantiate(binding_body(type), args[i]);
                expr const & arg_type = binding_domain(type);
                expr new_arg;
                if (!m_tctx.is_prop(arg_type)) {
                    auto it = m_subsingleton_elem_map.find(arg_type);
                    if (it != m_subsingleton_elem_map.end()) {
                        modified = (it->second != args[i]);
                        new_arg    = it->second;
                        lean_trace_d(name({"simplifier", "subsingleton"}), tout() << args[i] << " ==> " << new_arg << "\n";);
                    } else {
                        new_arg = args[i];
                        m_subsingleton_elem_map.insert(mk_pair(arg_type, args[i]));
                    }
                } else {
                    new_arg = args[i];
                }
                proof = mk_app(proof, new_arg);
                type = instantiate(binding_body(type), new_arg);
                break;
            }
            i++;
        });
    if (!modified)
        return simp_result(e);

    lean_assert(is_eq(type));
    buffer<expr> type_args;
    get_app_args(type, type_args);
    expr e_new = type_args[2];
    return simp_result(e_new, proof);
}

expr simplifier::remove_unnecessary_casts(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    ss_param_infos ss_infos = get_specialized_subsingleton_info(m_tctx, e);
    int i = -1;
    bool updated = false;
    for (ss_param_info const & ss_info : ss_infos) {
        i++;
        if (ss_info.is_subsingleton()) {
            while (is_constant(get_app_fn(args[i]))) {
                buffer<expr> cast_args;
                expr f_cast = get_app_args(args[i], cast_args);
                name n_f = const_name(f_cast);
                if (n_f == get_eq_rec_name() || n_f == get_eq_drec_name() || n_f == get_eq_nrec_name()) {
                    lean_assert(cast_args.size() == 6);
                    expr major_premise = cast_args[5];
                    expr f_major_premise = get_app_fn(major_premise);
                    if (is_constant(f_major_premise) && const_name(f_major_premise) == get_eq_refl_name()) {
                        args[i] = cast_args[3];
                        updated = true;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
    }
    if (!updated)
        return e;

    expr new_e = mk_app(f, args);
    lean_trace(name({"debug", "simplifier", "remove_casts"}), tout() << e << " ==> " << new_e << "\n";);

    return mk_app(f, args);
}

vm_obj simp_lemmas_simplify_core(vm_obj const & lemmas, vm_obj const & prove_fn, vm_obj const & rel_name, vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    try {
        type_context tctx    = mk_type_context_for(s, transparency_mode::Reducible);
        name rel             = to_name(rel_name);
        expr old_e           = to_expr(e);
        simp_result result   = simplify(tctx, rel, to_simp_lemmas(lemmas), prove_fn, old_e);

        if (result.get_new() != old_e) {
            result = finalize(tctx, rel, result);
            return mk_tactic_success(mk_vm_pair(to_obj(result.get_new()), to_obj(result.get_proof())), s);
        } else {
            return mk_tactic_exception("simp tactic failed to simplify", s);
        }
    } catch (exception & e) {
        return mk_tactic_exception(e, s);
    }
}

/* Setup and teardown */
void initialize_simplifier() {
    register_trace_class(name({"simplifier", "congruence"}));
    register_trace_class(name({"simplifier", "failure"}));
    register_trace_class(name({"simplifier", "failed"}));
    register_trace_class(name({"simplifier", "perm"}));
    register_trace_class(name({"simplifier", "canonize"}));
    register_trace_class(name({"simplifier", "context"}));
    register_trace_class(name({"simplifier", "prove"}));
    register_trace_class(name({"simplifier", "rewrite"}));
    register_trace_class(name({"simplifier", "rewrite", "assoc"}));
    register_trace_class(name({"simplifier", "theory"}));
    register_trace_class(name({"simplifier", "subsingleton"}));
    register_trace_class(name({"debug", "simplifier", "try_rewrite"}));
    register_trace_class(name({"debug", "simplifier", "try_rewrite", "assoc"}));
    register_trace_class(name({"debug", "simplifier", "try_congruence"}));
    register_trace_class(name({"debug", "simplifier", "remove_casts"}));

    g_simplify_prefix                         = new name{"simplify"};

    g_simplify_max_steps                      = new name{*g_simplify_prefix, "max_steps"};
    g_simplify_nary_assoc                     = new name{*g_simplify_prefix, "nary_assoc"};
    g_simplify_memoize                        = new name{*g_simplify_prefix, "memoize"};
    g_simplify_contextual                     = new name{*g_simplify_prefix, "contextual"};
    g_simplify_rewrite                        = new name{*g_simplify_prefix, "rewrite"};
    g_simplify_unsafe_nary                    = new name{*g_simplify_prefix, "unsafe_nary"};
    g_simplify_theory                         = new name{*g_simplify_prefix, "theory"};
    g_simplify_topdown                        = new name{*g_simplify_prefix, "topdown"};
    g_simplify_lift_eq                        = new name{*g_simplify_prefix, "lift_eq"};
    g_simplify_canonize_instances_fixed_point = new name{*g_simplify_prefix, "canonize_instances_fixed_point"};
    g_simplify_canonize_proofs_fixed_point    = new name{*g_simplify_prefix, "canonize_proofs_fixed_point"};
    g_simplify_canonize_subsingletons         = new name{*g_simplify_prefix, "canonize_subsingletons"};

    register_unsigned_option(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS,
                             "(simplify) max number of (large) steps in simplification");
    register_bool_option(*g_simplify_nary_assoc, LEAN_DEFAULT_SIMPLIFY_NARY_ASSOC,
                         "(simplify) use special treatment for operators that are instances of the is_associative typeclass");
    register_bool_option(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE,
                         "(simplify) memoize simplifications");
    register_bool_option(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL,
                         "(simplify) use contextual simplification");
    register_bool_option(*g_simplify_rewrite, LEAN_DEFAULT_SIMPLIFY_REWRITE,
                         "(simplify) rewrite with simp_lemmas");
    register_bool_option(*g_simplify_unsafe_nary, LEAN_DEFAULT_SIMPLIFY_UNSAFE_NARY,
                         "(simplify) assume all nested applications of associative operators "
                         "with the same head symbol are definitionally equal. "
                         "Will yield to invalid proofs if this assumption is not valid. "
                         "The kernel will detect these errors but only at a high-enough trust level.");
    register_bool_option(*g_simplify_theory, LEAN_DEFAULT_SIMPLIFY_THEORY,
                         "(simplify) use built-in theory simplification");
    register_bool_option(*g_simplify_topdown, LEAN_DEFAULT_SIMPLIFY_TOPDOWN,
                         "(simplify) use topdown simplification");
    register_bool_option(*g_simplify_lift_eq, LEAN_DEFAULT_SIMPLIFY_LIFT_EQ,
                         "(simplify) try simplifying with equality when no progress over other relation");
    register_bool_option(*g_simplify_canonize_instances_fixed_point, LEAN_DEFAULT_SIMPLIFY_CANONIZE_INSTANCES_FIXED_POINT,
                         "(simplify) canonize instances, replacing with the smallest seen so far until reaching a fixed point");
    register_bool_option(*g_simplify_canonize_proofs_fixed_point, LEAN_DEFAULT_SIMPLIFY_CANONIZE_PROOFS_FIXED_POINT,
                         "(simplify) canonize proofs, replacing with the smallest seen so far until reaching a fixed point. ");
    register_bool_option(*g_simplify_canonize_subsingletons, LEAN_DEFAULT_SIMPLIFY_CANONIZE_SUBSINGLETONS,
                         "(simplify) canonize_subsingletons");

    DECLARE_VM_BUILTIN(name({"simp_lemmas", "simplify_core"}), simp_lemmas_simplify_core);
}

void finalize_simplifier() {
    delete g_simplify_canonize_subsingletons;
    delete g_simplify_canonize_instances_fixed_point;
    delete g_simplify_canonize_proofs_fixed_point;
    delete g_simplify_lift_eq;
    delete g_simplify_topdown;
    delete g_simplify_theory;
    delete g_simplify_unsafe_nary;
    delete g_simplify_rewrite;
    delete g_simplify_contextual;
    delete g_simplify_memoize;
    delete g_simplify_nary_assoc;
    delete g_simplify_max_steps;
}

/* Entry point */
simp_result simplify(type_context & ctx, name const & rel, simp_lemmas const & simp_lemmas, vm_obj const & prove_fn, expr const & e) {
    return simplifier(ctx, rel, simp_lemmas, optional<vm_obj>(prove_fn))(e);
}

simp_result simplify(type_context & ctx, name const & rel, simp_lemmas const & simp_lemmas, expr const & e) {
    return simplifier(ctx, rel, simp_lemmas, optional<vm_obj>())(e);
}

}
