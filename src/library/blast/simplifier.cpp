/*
  Copyright (c) 2015 Daniel Selsam. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Daniel Selsam
*/
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/expr_lt.h"
#include "library/class_instance_resolution.h"
#include "library/relation_manager.h"
#include "library/blast/expr.h"
#include "library/blast/blast_exception.h"
#include "library/blast/blast.h"
#include "library/blast/simplifier.h"
#include "library/simplifier/simp_rule_set.h"
#include "library/simplifier/ceqv.h"
#include "library/app_builder.h"
#include "library/num.h"
#include "library/norm_num.h"
#include "util/flet.h"
#include "util/freset.h"
#include "util/pair.h"
#include "util/sexpr/option_declarations.h"
#include <functional>
#include <iostream>

#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_SIMPLIFY_MAX_STEPS 1000
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_TOP_DOWN
#define LEAN_DEFAULT_SIMPLIFY_TOP_DOWN false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE
#define LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_MEMOIZE
#define LEAN_DEFAULT_SIMPLIFY_MEMOIZE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL
#define LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS
#define LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_TRACE
#define LEAN_DEFAULT_SIMPLIFY_TRACE false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_FUSE
#define LEAN_DEFAULT_SIMPLIFY_FUSE false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_NUMERALS
#define LEAN_DEFAULT_SIMPLIFY_NUMERALS false
#endif

namespace lean {
namespace blast {

using simp::result;

/* Names */

static name * g_simplify_empty_namespace     = nullptr;
static name * g_simplify_unit_namespace      = nullptr;
static name * g_simplify_ac_namespace        = nullptr;
static name * g_simplify_som_namespace       = nullptr;
static name * g_simplify_numeral_namespace   = nullptr;

/* Options */

static name * g_simplify_max_steps     = nullptr;
static name * g_simplify_top_down      = nullptr;
static name * g_simplify_exhaustive    = nullptr;
static name * g_simplify_memoize       = nullptr;
static name * g_simplify_contextual    = nullptr;
static name * g_simplify_expand_macros = nullptr;
static name * g_simplify_trace         = nullptr;
static name * g_simplify_fuse          = nullptr;
static name * g_simplify_numerals      = nullptr;

unsigned get_simplify_max_steps() {
    return ios().get_options().get_unsigned(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS);
}

bool get_simplify_top_down() {
    return ios().get_options().get_bool(*g_simplify_top_down, LEAN_DEFAULT_SIMPLIFY_TOP_DOWN);
}

bool get_simplify_exhaustive() {
    return ios().get_options().get_bool(*g_simplify_exhaustive, LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE);
}

bool get_simplify_memoize() {
    return ios().get_options().get_bool(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE);
}

bool get_simplify_contextual() {
    return ios().get_options().get_bool(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL);
}

bool get_simplify_expand_macros() {
    return ios().get_options().get_bool(*g_simplify_expand_macros, LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS);
}

bool get_simplify_trace() {
    return ios().get_options().get_bool(*g_simplify_trace, LEAN_DEFAULT_SIMPLIFY_TRACE);
}

bool get_simplify_fuse() {
    return ios().get_options().get_bool(*g_simplify_fuse, LEAN_DEFAULT_SIMPLIFY_FUSE);
}

bool get_simplify_numerals() {
    return ios().get_options().get_bool(*g_simplify_numerals, LEAN_DEFAULT_SIMPLIFY_NUMERALS);
}

/* Miscellaneous helpers */

static bool is_add_app(expr const & e) {
    return is_const_app(e, get_add_name(), 4);
}

static bool is_mul_app(expr const & e) {
    return is_const_app(e, get_mul_name(), 4);
}

static bool is_neg_app(expr const & e) {
    return is_const_app(e, get_neg_name(), 3);
}

/* Main simplifier class */

class simplifier {
    blast_tmp_type_context                       m_tmp_tctx;
    app_builder                                  m_app_builder;
    name                                         m_rel;

    simp_rule_sets                               m_srss;
    simp_rule_sets                               m_ctx_srss;

    /* Logging */
    unsigned                                     m_num_steps{0};
    unsigned                                     m_depth{0};

    /* Options */
    unsigned                                     m_max_steps{get_simplify_max_steps()};
    bool                                         m_top_down{get_simplify_top_down()};
    bool                                         m_exhaustive{get_simplify_exhaustive()};
    bool                                         m_memoize{get_simplify_memoize()};
    bool                                         m_contextual{get_simplify_contextual()};
    bool                                         m_expand_macros{get_simplify_expand_macros()};
    bool                                         m_trace{get_simplify_trace()};
    bool                                         m_fuse{get_simplify_fuse()};
    bool                                         m_numerals{get_simplify_numerals()};

    /* Cache */
    struct key {
        name              m_rel;
        expr              m_e;
        unsigned          m_hash;

        key(name const & rel, expr const & e):
            m_rel(rel), m_e(e), m_hash(hash(rel.hash(), abstract_hash(e))) { }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.m_hash; }
    };

    struct key_eq_fn {
        bool operator()(key const & k1, key const & k2) const {
            return k1.m_rel == k2.m_rel && abstract_is_equal(k1.m_e, k2.m_e);
        }
    };

    typedef std::unordered_map<key, result, key_hash_fn, key_eq_fn> simplify_cache;
    simplify_cache m_cache;

    optional<result> cache_lookup(expr const & e);
    void cache_save(expr const & e, result const & r);

    /* Basic helpers */
    bool using_eq() { return m_rel == get_eq_name(); }

    bool is_dependent_fn(expr const & f) {
        expr f_type = m_tmp_tctx->whnf(m_tmp_tctx->infer(f));
        lean_assert(is_pi(f_type));
        return has_free_vars(binding_body(f_type));
    }

    simp_rule_sets add_to_srss(simp_rule_sets const & _srss, buffer<expr> & ls) {
        simp_rule_sets srss = _srss;
        for (unsigned i = 0; i < ls.size(); i++) {
            expr & l = ls[i];
            if (m_trace) {
                ios().get_diagnostic_channel() << "Local: " << l << " : " << mlocal_type(l) << "\n";
            }
            tmp_type_context tctx(env(), ios());
            try {
                // TODO(Leo,Daniel): should we allow the user to set the priority of local lemmas
                srss = add(tctx, srss, mlocal_name(l), tctx.infer(l), l, LEAN_SIMP_DEFAULT_PRIORITY);
            } catch (exception e) {
            }
        }
        return srss;
    }

    expr unfold_reducible_instances(expr const & e);
    expr remove_unnecessary_casts(expr const & e);

    bool instantiate_emetas(blast_tmp_type_context & tmp_tctx, unsigned num_emeta,
                            list<expr> const & emetas, list<bool> const & instances);

    /* Results */
    result lift_from_eq(expr const & e_old, result const & r_eq);
    result join(result const & r1, result const & r2);
    result funext(result const & r, expr const & l);
    result finalize(result const & r);

    /* Simplification */
    result simplify(expr const & e, simp_rule_sets const & srss);
    result simplify(expr const & e, bool is_root);
    result simplify_lambda(expr const & e);
    result simplify_pi(expr const & e);
    result simplify_app(expr const & e);
    result simplify_fun(expr const & e);
    optional<result> simplify_numeral(expr const & e);

    /* Proving */
    optional<expr> prove(expr const & thm);
    optional<expr> prove(expr const & thm, simp_rule_sets const & srss);

    /* Rewriting */
    result rewrite(expr const & e);
    result rewrite(expr const & e, simp_rule_sets const & srss);
    result rewrite(expr const & e, simp_rule const & sr);

    /* Congruence */
    result congr_fun_arg(result const & r_f, result const & r_arg);
    result congr(result const & r_f, result const & r_arg);
    result congr_fun(result const & r_f, expr const & arg);
    result congr_arg(expr const & f, result const & r_arg);
    result congr_funs(result const & r_f, buffer<expr> const & args);

    result try_congrs(expr const & e);
    result try_congr(expr const & e, congr_rule const & cr);

    template<typename F>
    optional<result> synth_congr(expr const & e, F && simp);

    /* Fusion */
    result maybe_fuse(expr const & e, bool is_root);
    result fuse(expr const & e);
    expr_pair split_summand(expr const & e, expr const & f_mul, expr const & one);


public:
    simplifier(name const & rel): m_app_builder(*m_tmp_tctx), m_rel(rel) { }
    result operator()(expr const & e, simp_rule_sets const & srss)  { return simplify(e, srss); }
};

/* Cache */

optional<result> simplifier::cache_lookup(expr const & e) {
    auto it = m_cache.find(key(m_rel, e));
    if (it == m_cache.end()) return optional<result>();
    /* The cache ignores subsingletons, so we may need to
       synthesize a congruence lemma. */
    expr e_old = it->first.m_e;
    result r_old = it->second;
    lean_assert(abstract_is_equal(e, e_old));
    if (e == e_old) return optional<result>(r_old);
    lean_assert(is_app(e_old));
    buffer<expr> new_args, old_args;
    expr const & f_new = get_app_args(e, new_args);
    DEBUG_CODE(expr const & f_old =) get_app_args(e_old, old_args);
    lean_assert(f_new == f_old);
    auto congr_lemma = mk_congr_lemma(f_new, new_args.size());
    if (!congr_lemma) return optional<result>();
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();

    unsigned i = 0;
    for_each(congr_lemma->get_arg_kinds(), [&](congr_arg_kind const & ckind) {
            if (ckind != congr_arg_kind::Cast) {
                lean_assert(new_args[i] == old_args[i]);
            }
            proof = mk_app(proof, new_args[i]);
            type = instantiate(binding_body(type), new_args[i]);
            expr rfl;
            switch (ckind) {
            case congr_arg_kind::Fixed:
                break;
            case congr_arg_kind::Eq:
                rfl = m_app_builder.mk_eq_refl(old_args[i]);
                proof = mk_app(proof, old_args[i], rfl);
                type = instantiate(binding_body(type), old_args[i]);
                type = instantiate(binding_body(type), rfl);
                break;
            case congr_arg_kind::Cast:
                proof = mk_app(proof, old_args[i]);
                type = instantiate(binding_body(type), old_args[i]);
                break;
            }
            i++;
        });

    lean_assert(is_eq(type));
    result r_congr = result(e_old, proof);
    return optional<result>(join(r_congr, r_old));
}

void simplifier::cache_save(expr const & e, result const & r) {
    m_cache.insert(mk_pair(key(m_rel, e), r));
}

/* Results */

result simplifier::lift_from_eq(expr const & e_old, result const & r_eq) {
    if (!r_eq.has_proof()) return r_eq;
    lean_assert(r_eq.has_proof());
    /* r_eq.get_proof() : e_old = r_eq.get_new() */
    /* goal : e_old <m_rel> r_eq.get_new() */
    expr l = m_tmp_tctx->mk_tmp_local(m_tmp_tctx->infer(e_old));
    expr motive_local = m_app_builder.mk_app(m_rel, e_old, l);
    /* motive = fun y, e_old <m_rel> y */
    expr motive = Fun(l, motive_local);
    /* Rxx = x <m_rel> x */
    expr Rxx = m_app_builder.mk_refl(m_rel, e_old);
    expr pf = m_app_builder.mk_eq_rec(motive, Rxx, r_eq.get_proof());
    return result(r_eq.get_new(), pf);
}

result simplifier::join(result const & r1, result const & r2) {
    /* Assumes that both results are with respect to the same relation */
    if (!r1.has_proof()) {
        return r2;
    } else if (!r2.has_proof()) {
        lean_assert(r1.has_proof());
        return result(r2.get_new(), r1.get_proof());
    } else {
        /* If they both have proofs, we need to glue them together with transitivity. */
        lean_assert(r1.has_proof() && r2.has_proof());
        expr trans = m_app_builder.mk_trans(m_rel, r1.get_proof(), r2.get_proof());
        return result(r2.get_new(), trans);
    }
}

result simplifier::funext(result const & r, expr const & l) {
    // theorem funext {f₁ f₂ : Πx : A, B x} : (∀x, f₁ x = f₂ x) → f₁ = f₂ :=
    expr e  = Fun(l, r.get_new());
    if (!r.has_proof()) return result(e);
    expr pf = m_app_builder.mk_app(get_funext_name(), Fun(l, r.get_proof()));
    return result(e, pf);
}

result simplifier::finalize(result const & r) {
    if (r.has_proof()) return r;
    expr pf = m_app_builder.mk_refl(m_rel, r.get_new());
    return result(r.get_new(), pf);
}

/* Simplification */

result simplifier::simplify(expr const & e, simp_rule_sets const & srss) {
    flet<simp_rule_sets> set_srss(m_srss, srss);
    freset<simplify_cache> reset(m_cache);
    return simplify(e, true);
}

result simplifier::simplify(expr const & e, bool is_root) {
    m_num_steps++;
    flet<unsigned> inc_depth(m_depth, m_depth+1);

    if (m_trace) {
        ios().get_diagnostic_channel() << m_depth << "." << m_rel << ": " << e << "\n";
    }

    if (m_num_steps > m_max_steps)
        throw blast_exception("simplifier failed, maximum number of steps exceeded", e);

    if (m_memoize) {
        if (auto it = cache_lookup(e)) return *it;
    }

    if (m_numerals && using_eq()) {
        if (auto r = simplify_numeral(e)) {
            return *r;
        }
    }

    result r(e);

    if (m_top_down) r = join(r, rewrite(whnf(r.get_new())));

    r.update(whnf(r.get_new()));

    switch (r.get_new().kind()) {
    case expr_kind::Local:
    case expr_kind::Meta:
    case expr_kind::Sort:
    case expr_kind::Constant:
        // no-op
        break;
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Macro:
        if (m_expand_macros) {
            if (auto m = m_tmp_tctx->expand_macro(e)) r = join(r, simplify(whnf(*m), is_root));
        }
        break;
    case expr_kind::Lambda:
        if (using_eq()) r = join(r, simplify_lambda(r.get_new()));
        break;
    case expr_kind::Pi:
        r = join(r, simplify_pi(r.get_new()));
        break;
    case expr_kind::App:
        r = join(r, simplify_app(r.get_new()));
        break;
    }

    if (!m_top_down) r = join(r, rewrite(whnf(r.get_new())));

    if (r.get_new() == e && !using_eq()) {
        result r_eq;
        {
            flet<name> use_eq(m_rel, get_eq_name());
            r_eq = simplify(r.get_new(), is_root);
        }
        r = join(r, lift_from_eq(r.get_new(), r_eq));
    }

    if (m_exhaustive && r.has_proof()) r = join(r, simplify(r.get_new(), is_root));

    if (m_memoize) cache_save(e, r);

    if (m_fuse && using_eq()) r = join(r, maybe_fuse(r.get_new(), is_root));

    return r;
}

result simplifier::simplify_lambda(expr const & e) {
    lean_assert(is_lambda(e));
    expr t = e;

    buffer<expr> ls;
    while (is_lambda(t)) {
        expr d = instantiate_rev(binding_domain(t), ls.size(), ls.data());
        expr l = m_tmp_tctx->mk_tmp_local(d, binding_info(t));
        ls.push_back(l);
        t = instantiate(binding_body(t), l);
    }

    result r = simplify(t, false);
    for (int i = ls.size() - 1; i >= 0; --i) r = funext(r, ls[i]);
    return r;
}

result simplifier::simplify_pi(expr const & e) {
    lean_assert(is_pi(e));
    return try_congrs(e);
}

expr simplifier::unfold_reducible_instances(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    fun_info f_info = get_fun_info(f, args.size());
    int i = -1;
    for_each(f_info.get_params_info(), [&](param_info const & p_info) {
            i++;
            if (p_info.is_inst_implicit() && !p_info.is_subsingleton()) {
                args[i] = blast::normalize(args[i]);
            }
        });
    return mk_app(f, args);
}

result simplifier::simplify_app(expr const & _e) {
    lean_assert(is_app(_e));
    expr e = unfold_reducible_instances(_e);

    /* (1) Try user-defined congruences */
    result r_user = try_congrs(e);
    if (r_user.has_proof()) {
        if (using_eq()) return join(r_user, simplify_fun(r_user.get_new()));
        else return r_user;
    }

    /* (2) Synthesize congruence lemma */
    if (using_eq()) {
        optional<result> r_args = synth_congr(e, [&](expr const & e) {
                return simplify(e, false);
            });
        if (r_args) return join(*r_args, simplify_fun(r_args->get_new()));
    }

    /* (3) Fall back on generic binary congruence */
    if (using_eq()) {
        expr const & f = app_fn(e);
        expr const & arg = app_arg(e);

        // TODO(dhs): it is not clear if this recursive call should be considered
        // a root or not, though does not matter since if + were being applied,
        // we would have synthesized a congruence rule in step (2).
        result r_f = simplify(f, false);

        if (is_dependent_fn(f)) {
            if (r_f.has_proof()) return congr_fun(r_f, arg);
            else return mk_app(r_f.get_new(), arg);
        } else {
            result r_arg = simplify(arg, false);
            return congr_fun_arg(r_f, r_arg);
        }
    }
    return result(e);
}

result simplifier::simplify_fun(expr const & e) {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    result r_f = simplify(f, true);
    return congr_funs(r_f, args);
}

optional<result> simplifier::simplify_numeral(expr const & e) {
    if (is_num(e)) { return optional<result>(result(e)); }

    try {
        expr_pair r = mk_norm_num(*m_tmp_tctx, e);
        return optional<result>(result(r.first, r.second));
    } catch (exception e) {
        return optional<result>();
    }
}

/* Proving */

optional<expr> simplifier::prove(expr const & thm) {
    flet<name> set_name(m_rel, get_iff_name());
    result r_cond = simplify(thm, true);
    if (is_constant(r_cond.get_new()) && const_name(r_cond.get_new()) == get_true_name()) {
        expr pf = m_app_builder.mk_app(get_iff_elim_right_name(),
                                       finalize(r_cond).get_proof(),
                                       mk_constant(get_true_intro_name()));
        return some_expr(pf);
    }
    return none_expr();
}

optional<expr> simplifier::prove(expr const & thm, simp_rule_sets const & srss) {
    flet<name> set_name(m_rel, get_iff_name());
    result r_cond = simplify(thm, srss);
    if (is_constant(r_cond.get_new()) && const_name(r_cond.get_new()) == get_true_name()) {
        expr pf = m_app_builder.mk_app(get_iff_elim_right_name(),
                                       finalize(r_cond).get_proof(),
                                       mk_constant(get_true_intro_name()));
        return some_expr(pf);
    }
    return none_expr();
}

/* Rewriting */

result simplifier::rewrite(expr const & e) {
    result r(e);
    while (true) {
        result r_ctx = rewrite(r.get_new(), m_ctx_srss);
        result r_new = rewrite(r_ctx.get_new(), m_srss);
        if (!r_ctx.has_proof() && !r_new.has_proof()) break;
        r = join(join(r, r_ctx), r_new);
    }
    return r;
}

result simplifier::rewrite(expr const & e, simp_rule_sets const & srss) {
    result r(e);

    simp_rule_set const * sr = srss.find(m_rel);
    if (!sr) return r;

    list<simp_rule> const * srs = sr->find_simp(e);
    if (!srs) return r;

    for_each(*srs, [&](simp_rule const & sr) {
            result r_new = rewrite(r.get_new(), sr);
            if (!r_new.has_proof()) return;
            r = join(r, r_new);
        });
    return r;
}

result simplifier::rewrite(expr const & e, simp_rule const & sr) {
    blast_tmp_type_context tmp_tctx(sr.get_num_umeta(), sr.get_num_emeta());

    if (!tmp_tctx->is_def_eq(e, sr.get_lhs())) return result(e);

    if (m_trace) {
        expr new_lhs = tmp_tctx->instantiate_uvars_mvars(sr.get_lhs());
        expr new_rhs = tmp_tctx->instantiate_uvars_mvars(sr.get_rhs());
        ios().get_diagnostic_channel()
            << "REW(" << sr.get_id() << ") "
            << "[" << new_lhs << " =?= " << new_rhs << "]\n";
    }

    if (!instantiate_emetas(tmp_tctx, sr.get_num_emeta(), sr.get_emetas(), sr.get_instances())) return result(e);

    for (unsigned i = 0; i < sr.get_num_umeta(); i++) {
        if (!tmp_tctx->is_uvar_assigned(i)) return result(e);
    }

    expr new_lhs = tmp_tctx->instantiate_uvars_mvars(sr.get_lhs());
    expr new_rhs = tmp_tctx->instantiate_uvars_mvars(sr.get_rhs());

    if (sr.is_perm()) {
        if (!is_lt(new_rhs, new_lhs, false))
            return result(e);
    }

    expr pf = tmp_tctx->instantiate_uvars_mvars(sr.get_proof());
    return result(new_rhs, pf);
}

/* Congruence */

result simplifier::congr_fun_arg(result const & r_f, result const & r_arg) {
    if (!r_f.has_proof() && !r_arg.has_proof()) return result(mk_app(r_f.get_new(), r_arg.get_new()));
    else if (!r_f.has_proof()) return congr_arg(r_f.get_new(), r_arg);
    else if (!r_arg.has_proof()) return congr_fun(r_f, r_arg.get_new());
    else return congr(r_f, r_arg);
}

result simplifier::congr(result const & r_f, result const & r_arg) {
    lean_assert(r_f.has_proof() && r_arg.has_proof());
    // theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
    expr e  = mk_app(r_f.get_new(), r_arg.get_new());
    expr pf = m_app_builder.mk_congr(r_f.get_proof(), r_arg.get_proof());
    return result(e, pf);
}

result simplifier::congr_fun(result const & r_f, expr const & arg) {
    lean_assert(r_f.has_proof());
    // theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
    expr e  = mk_app(r_f.get_new(), arg);
    expr pf = m_app_builder.mk_congr_fun(r_f.get_proof(), arg);
    return result(e, pf);
}

result simplifier::congr_arg(expr const & f, result const & r_arg) {
    lean_assert(r_arg.has_proof());
    // theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂
    expr e  = mk_app(f, r_arg.get_new());
    expr pf = m_app_builder.mk_congr_arg(f, r_arg.get_proof());
    return result(e, pf);
}

/* Note: handles reflexivity */
result simplifier::congr_funs(result const & r_f, buffer<expr> const & args) {
    // congr_fun : ∀ {A : Type} {B : A → Type} {f g : Π (x : A), B x}, f = g → (∀ (a : A), f a = g a)
    expr e = r_f.get_new();
    for (unsigned i = 0; i < args.size(); ++i) {
        e  = mk_app(e, args[i]);
    }
    if (!r_f.has_proof()) return result(e);
    expr pf = r_f.get_proof();
    for (unsigned i = 0; i < args.size(); ++i) {
        pf = m_app_builder.mk_app(get_congr_fun_name(), pf, args[i]);
    }
    return result(e, pf);
}

result simplifier::try_congrs(expr const & e) {
    simp_rule_set const * sr = get_simp_rule_sets(env()).find(m_rel);
    if (!sr) return result(e);

    list<congr_rule> const * crs = sr->find_congr(e);
    if (!crs) return result(e);

    result r(e);
    for_each(*crs, [&](congr_rule const & cr) {
            if (r.has_proof()) return;
            r = try_congr(e, cr);
        });
    return r;
}

result simplifier::try_congr(expr const & e, congr_rule const & cr) {
    blast_tmp_type_context tmp_tctx(cr.get_num_umeta(), cr.get_num_emeta());

    if (!tmp_tctx->is_def_eq(e, cr.get_lhs())) return result(e);

    if (m_trace) {
        expr new_lhs = tmp_tctx->instantiate_uvars_mvars(cr.get_lhs());
        expr new_rhs = tmp_tctx->instantiate_uvars_mvars(cr.get_rhs());
        ios().get_diagnostic_channel()
            << "CONGR(" << cr.get_id() << ") "
            << "[" << new_lhs << " =?= " << new_rhs << "]\n";
    }

    /* First, iterate over the congruence hypotheses */
    bool failed = false;
    bool simplified = false;
    list<expr> const & congr_hyps = cr.get_congr_hyps();
    for_each(congr_hyps, [&](expr const & m) {
            if (failed) return;
            buffer<expr> ls;
            expr m_type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));

            while (is_pi(m_type)) {
                expr d = instantiate_rev(binding_domain(m_type), ls.size(), ls.data());
                expr l = tmp_tctx->mk_tmp_local(d, binding_info(m_type));
                lean_assert(!has_metavar(l));
                ls.push_back(l);
                m_type = instantiate(binding_body(m_type), l);
            }

            expr h_rel, h_lhs, h_rhs;
            lean_verify(is_simp_relation(env(), m_type, h_rel, h_lhs, h_rhs) && is_constant(h_rel));
            {
                flet<name> set_name(m_rel, const_name(h_rel));
                flet<simp_rule_sets> set_ctx_srss(m_ctx_srss, add_to_srss(m_ctx_srss, ls));

                h_lhs = tmp_tctx->instantiate_uvars_mvars(h_lhs);
                lean_assert(!has_metavar(h_lhs));

                result r_congr_hyp = simplify(h_lhs, m_srss);
                if (r_congr_hyp.has_proof()) simplified = true;
                r_congr_hyp = finalize(r_congr_hyp);
                expr hyp = finalize(r_congr_hyp).get_proof();

                if (!tmp_tctx->is_def_eq(m, Fun(ls, hyp))) failed = true;
            }
        });

    if (failed || !simplified) return result(e);

    if (!instantiate_emetas(tmp_tctx, cr.get_num_emeta(), cr.get_emetas(), cr.get_instances())) return result(e);

    for (unsigned i = 0; i < cr.get_num_umeta(); i++) {
        if (!tmp_tctx->is_uvar_assigned(i)) return result(e);
    }

    expr e_s = tmp_tctx->instantiate_uvars_mvars(cr.get_rhs());
    expr pf = tmp_tctx->instantiate_uvars_mvars(cr.get_proof());
    return result(e_s, pf);
}

bool simplifier::instantiate_emetas(blast_tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas,
                                    list<bool> const & instances) {
    bool failed = false;
    unsigned i = num_emeta;
    for_each2(emetas, instances, [&](expr const & m, bool const & is_instance) {
            i--;
            if (failed) return;
            expr m_type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));
            lean_assert(!has_metavar(m_type));

            if (is_instance) {
                if (auto v = tmp_tctx->mk_class_instance(m_type)) {
                    if (!tmp_tctx->force_assign(m, *v)) {
                        if (m_trace) {
                            ios().get_diagnostic_channel() << "unable to assign instance for: " << m_type << "\n";
                        }
                        failed = true;
                        return;
                    }
                } else {
                    if (m_trace) {
                        ios().get_diagnostic_channel() << "unable to synthesize instance for: " << m_type << "\n";
                    }
                    failed = true;
                    return;
                }
            }

            if (tmp_tctx->is_mvar_assigned(i)) return;

            if (tmp_tctx->is_prop(m_type)) {
                if (auto pf = prove(m_type)) {
                    lean_verify(tmp_tctx->is_def_eq(m, *pf));
                    return;
                }
            }

            if (m_trace) {
                ios().get_diagnostic_channel() << "failed to assign: " << m << " : " << m_type << "\n";
            }

            failed = true;
            return;
        });

    return !failed;
}

template<typename F>
optional<result> simplifier::synth_congr(expr const & e, F && simp) {
    static_assert(std::is_same<typename std::result_of<F(expr const & e)>::type, result>::value,
                  "synth_congr: simp must take expressions to results");
    lean_assert(is_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    auto congr_lemma = mk_congr_lemma_for_simp(f, args.size());
    if (!congr_lemma) return optional<result>();
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    unsigned i = 0;
    bool has_proof = false;
    bool has_cast = false;
    buffer<expr> locals;
    for_each(congr_lemma->get_arg_kinds(), [&](congr_arg_kind const & ckind) {
            proof = mk_app(proof, args[i]);
            type = instantiate(binding_body(type), args[i]);
            if (ckind == congr_arg_kind::Eq) {
                result r_arg = simp(args[i]);
                if (r_arg.has_proof()) has_proof = true;
                r_arg = finalize(r_arg);
                proof = mk_app(proof, r_arg.get_new(), r_arg.get_proof());
                type = instantiate(binding_body(type), r_arg.get_new());
                type = instantiate(binding_body(type), r_arg.get_proof());
            } else if (ckind == congr_arg_kind::Cast) {
                has_cast = true;
            }
            i++;
        });
    lean_assert(is_eq(type));
    buffer<expr> type_args;
    get_app_args(type, type_args);
    expr e_new = remove_unnecessary_casts(type_args[2]);
    if (has_proof) return optional<result>(result(e_new, proof));
    else return optional<result>(result(e_new));
}

expr simplifier::remove_unnecessary_casts(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    fun_info f_info = get_fun_info(f, args.size());
    int i = -1;
    for_each(f_info.get_params_info(), [&](param_info const & p_info) {
            i++;
            if (p_info.is_subsingleton()) {
                while (is_constant(get_app_fn(args[i]))) {
                    buffer<expr> cast_args;
                    expr f_cast = get_app_args(args[i], cast_args);
                    name n_f = const_name(f_cast);
                    if (n_f == get_eq_rec_name() || n_f == get_eq_drec_name() || n_f == get_eq_nrec_name()) {
                        lean_assert(cast_args.size() == 6);
                        expr major_premise = cast_args[5];
                        expr f_major_premise = get_app_fn(major_premise);
                        if (is_constant(f_major_premise) && const_name(f_major_premise) == get_eq_refl_name())
                            args[i] = cast_args[3];
                        else
                            return;
                    } else {
                        return;
                    }
                }
            }
        });
    return mk_app(f, args);
}

/* Fusion */

result simplifier::maybe_fuse(expr const & e, bool is_root) {
    if (!is_app(e)) return result(e);
    if (is_root && is_add_app(e)) return fuse(e);
    if (!is_root && is_add_app(e)) return result(e);
    lean_assert(!is_add_app(e));
    /* At this point we know we are an application of something other than + */
    optional<result> r = synth_congr(e, [&](expr const & arg) {
            if (is_add_app(arg)) return fuse(arg);
            else return result(arg);
        });
    if (r) return *r;
    else return result(e);
}

result simplifier::fuse(expr const & e) {
    lean_assert(is_add_app(e));
//    ios().get_diagnostic_channel() << "FUSE: " << e << "\n\n";
    flet<bool> no_recursive_fusion(m_fuse, false);

    /* Note: we assume all negations are on the outside of the summands */

    /* Example
       1. Input (e): n1 * x1 * n2 * x2 + x3 + - (x1 * x2 * n3) + (- x3) + x4
       2. Split summands: (n1 * n2) * (x1 * x2) + 1 * x3 + (- n3) * (x1 * x2) + (- 1) * x3 + 1 * x4
       3. Group by variable (e_grp): ((n1 * n2) * (x1 * x2) + (- n3) * (x1 * x2)) + (1 * x3 + (-1) * x3) + x4
       4. Introduce locals (e_grp_ls): ((n1 * n2) * l1 + (- n3) * l1) + (1 * l2 + (-1) * l2) + l3
       5. Fuse (e_fused_ls): (n1 * n2 + (- n3)) * l1 + (1 + (- 1)) * l2 + 1 * l3
       6. Simplify coefficients (e_simp_ls): (n1 * n2 + (- n3)) * l1 + l3
       7. Instantiate locals (e_simp): (n1 * n2 + (- n3)) * (x1 * x2) + x4

       Proofs
       1. Prove (1) == (3) using simplify with [ac]
       2. Prove (4) == (5) using simplify with [som]
       3. Prove (5) == (6) using simplify with [numeral]
       4. Prove (4) == (6) by transitivity of proofs (2) and (3)
       5. Prove (3) == (7) by instantiating proof (4)
       6. Prove (1) == (7) by transitivity of proofs (1) and (5)
    */

    /* Construct useful expressions */
    buffer<expr> args;
    get_app_args(e, args);
    expr T = args[0];
    expr f_add, f_mul, zero, one;
    try {
        f_add = m_app_builder.mk_partial_add(T);
        f_mul = m_app_builder.mk_partial_mul(T);
        zero = m_app_builder.mk_zero(T);
        one = m_app_builder.mk_one(T);
        expr left_distrib = m_app_builder.mk_partial_left_distrib(T);
    } catch (app_builder_exception & ex) {
        ios().get_diagnostic_channel() << "Cannot synthesize necessary instances\n";
        return result(e);
    }

    /* (1 ==> 2) Split each summand into (a) numerals and (b) variables */
    buffer<expr> numerals;
    buffer<expr> variables;
    expr s = e;
    while (is_add_app(s)) {
        buffer<expr> args;
        expr f = get_app_args(s, args);
        auto n_v = split_summand(args[2], f_mul, one);
        numerals.push_back(n_v.first);
        variables.push_back(n_v.second);
        s = args[3];
    }
    auto n_v = split_summand(s, f_mul, one);
    numerals.push_back(n_v.first);
    variables.push_back(n_v.second);
    lean_assert(numerals.size() == variables.size());

    /* (2 ==> 3, 4, 5) Group the summands by variable */
    expr_bi_struct_map<list<expr> > variable_to_numerals;
    for (unsigned i = 0; i < numerals.size(); i++) {
        auto it = variable_to_numerals.find(variables[i]);
        if (it != variable_to_numerals.end()) it->second = cons(numerals[i], it->second);
        else variable_to_numerals.insert({variables[i], list<expr>(numerals[i])});
    }

    expr e_grp = zero;
    expr e_grp_ls = zero;
    expr e_fused_ls = zero;

    buffer<expr> locals;
    variables.clear();
    for (auto v_ns : variable_to_numerals) {
        expr local;
        if (!is_one(v_ns.first)) {
            local = m_tmp_tctx->mk_tmp_local(T);
            locals.push_back(local);
            variables.push_back(v_ns.first);
        } else {
            local = v_ns.first;
        }

        expr term = zero;
        expr term_ls = zero;
        expr term_fused_ls = zero;
        for_each(v_ns.second, [&](expr const & n) {
                term = mk_app(f_add, mk_app(f_mul, v_ns.first, n), term);
                term_ls = mk_app(f_add, mk_app(f_mul, local, n), term_ls);
                term_fused_ls = mk_app(f_add, n, term_fused_ls);
            });
        e_grp = mk_app(f_add, term, e_grp);
        e_grp_ls = mk_app(f_add, term_ls, e_grp_ls);
        e_fused_ls = mk_app(f_add, mk_app(f_mul, term_fused_ls, local), e_fused_ls);
    }

    /* Prove (1) == (3) using simplify with [ac] */
    flet<bool> no_simplify_numerals(m_numerals, false);
    auto pf_1_3 = prove(m_app_builder.mk_eq(e, e_grp),
                        get_simp_rule_sets(env(), ios(), *g_simplify_ac_namespace));
    if (!pf_1_3) {
        diagnostic(env(), ios()) << e << "\n\n =?=\n\n" << e_grp << "\n";
        throw blast_exception("Failed to prove (1) == (3) during fusion", e);
    }

    /* Prove (4) == (5) using simplify with [som] */
    auto pf_4_5 = prove(m_app_builder.mk_eq(e_grp_ls, e_fused_ls),
                        get_simp_rule_sets(env(), ios(), *g_simplify_som_namespace));
    if (!pf_4_5) {
        diagnostic(env(), ios()) << e_grp_ls << "\n\n =?=\n\n" << e_fused_ls << "\n";
        throw blast_exception("Failed to prove (4) == (5) during fusion", e);
    }

    /* Prove (5) == (6) using simplify with [numeral] */
    flet<bool> simplify_numerals(m_numerals, true);
    result r_simp_ls = simplify(e_fused_ls, get_simp_rule_sets(env(), ios(), *g_simplify_ac_namespace));

    /* Prove (4) == (6) by transitivity of proofs (2) and (3) */
    expr pf_4_6;
    if (!r_simp_ls.has_proof()) pf_4_6 = *pf_4_5;
    else pf_4_6 = m_app_builder.mk_eq_trans(*pf_4_5, r_simp_ls.get_proof());

    /* Prove (3) == (7) by instantiating proof (4) */
    expr pf_3_7 = mk_app(Fun(locals, pf_4_6), variables);

    /* Prove (1) == (7) by transitivity of proofs (1) and (5) */
    expr pf_1_7 = m_app_builder.mk_eq_trans(*pf_1_3, pf_3_7);

    return result(mk_app(Fun(locals, r_simp_ls.get_new()), variables), pf_1_7);
}

expr_pair simplifier::split_summand(expr const & e, expr const & f_mul, expr const & one) {
    /* [e] is a possibly negated, possibly null product, where some of the multiplicands are numerals
       and the rest are treated as variables. This method does the following conversion:
       - (x1 * n1 * x2 * n3) ==> (-1 * n1 * n3) * (x1 * x2) */
    expr s = e;
    expr numeral = one;
    expr variable = one;
    if (is_neg_app(s)) {
        buffer<expr> args;
        get_app_args(s, args);
        numeral = m_app_builder.mk_app(get_neg_name(), one);
        s = args[2];
    }
    while (is_mul_app(s)) {
        buffer<expr> args;
        get_app_args(s, args);
        expr const & multiplicand = args[2];
        if (is_num(multiplicand)) {
            numeral = mk_app(f_mul, multiplicand, numeral);
        } else {
            if (variable == one) variable = multiplicand;
            else variable = mk_app(f_mul, multiplicand, variable);
        }
        s = args[3];
    }
    if (is_num(s)) {
        numeral = mk_app(f_mul, s, numeral);
    } else {
        if (variable == one) variable = s;
        else variable = mk_app(f_mul, s, variable);
    }
    return mk_pair(numeral, variable);
}

/* Setup and teardown */

void initialize_simplifier() {
    g_simplify_empty_namespace     = new name{"simplifier", "empty"};
    g_simplify_unit_namespace      = new name{"simplifier", "unit"};
    g_simplify_ac_namespace        = new name{"simplifier", "ac"};
    g_simplify_som_namespace       = new name{"simplifier", "som"};
    g_simplify_numeral_namespace   = new name{"simplifier", "numeral"};

    g_simplify_max_steps     = new name{"simplify", "max_steps"};
    g_simplify_top_down      = new name{"simplify", "top_down"};
    g_simplify_exhaustive    = new name{"simplify", "exhaustive"};
    g_simplify_memoize       = new name{"simplify", "memoize"};
    g_simplify_contextual    = new name{"simplify", "contextual"};
    g_simplify_expand_macros = new name{"simplify", "expand_macros"};
    g_simplify_trace         = new name{"simplify", "trace"};
    g_simplify_fuse          = new name{"simplify", "fuse"};
    g_simplify_numerals      = new name{"simplify", "numerals"};

    register_unsigned_option(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS,
                             "(simplify) max allowed steps in simplification");
    register_bool_option(*g_simplify_top_down, LEAN_DEFAULT_SIMPLIFY_TOP_DOWN,
                         "(simplify) use top-down rewriting instead of bottom-up");
    register_bool_option(*g_simplify_exhaustive, LEAN_DEFAULT_SIMPLIFY_EXHAUSTIVE,
                         "(simplify) rewrite exhaustively");
    register_bool_option(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE,
                         "(simplify) memoize simplifications");
    register_bool_option(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL,
                         "(simplify) use contextual simplification");
    register_bool_option(*g_simplify_expand_macros, LEAN_DEFAULT_SIMPLIFY_EXPAND_MACROS,
                         "(simplify) expand macros");
    register_bool_option(*g_simplify_trace, LEAN_DEFAULT_SIMPLIFY_TRACE,
                         "(simplify) trace");
    register_bool_option(*g_simplify_fuse, LEAN_DEFAULT_SIMPLIFY_FUSE,
                         "(simplify) fuse addition in distrib structures");
    register_bool_option(*g_simplify_numerals, LEAN_DEFAULT_SIMPLIFY_NUMERALS,
                         "(simplify) simplify (+, *, -, /) over numerals");
}

void finalize_simplifier() {
    delete g_simplify_numerals;
    delete g_simplify_fuse;
    delete g_simplify_trace;
    delete g_simplify_expand_macros;
    delete g_simplify_contextual;
    delete g_simplify_memoize;
    delete g_simplify_exhaustive;
    delete g_simplify_top_down;
    delete g_simplify_max_steps;

    delete g_simplify_numeral_namespace;
    delete g_simplify_som_namespace;
    delete g_simplify_ac_namespace;
    delete g_simplify_unit_namespace;
    delete g_simplify_empty_namespace;
}

/* Entry point */
result simplify(name const & rel, expr const & e, simp_rule_sets const & srss) {
    return simplifier(rel)(e, srss);
}

}}
