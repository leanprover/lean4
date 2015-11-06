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
#include "util/flet.h"
#include "util/pair.h"
#include "util/sexpr/option_declarations.h"
#include <array>
#include <map>
#include <iostream> // TODO just for occasional debugging

#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_SIMPLIFY_MAX_STEPS 100
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

namespace lean {
namespace blast {

using simp::result;

/* Options */

static name * g_simplify_max_steps     = nullptr;
static name * g_simplify_top_down      = nullptr;
static name * g_simplify_exhaustive    = nullptr;
static name * g_simplify_memoize       = nullptr;
static name * g_simplify_contextual    = nullptr;
static name * g_simplify_expand_macros = nullptr;
static name * g_simplify_trace         = nullptr;

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

/* Main simplifier class */

class simplifier {
    blast_tmp_type_context                       m_tmp_tctx;
    app_builder                                  m_app_builder;
    branch                                       m_branch;
    name                                         m_rel;

    list<expr>                                   m_local_ctx;

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
    
    /* Cache */
    typedef expr_bi_struct_map<result>           simplify_cache;
    std::map<name,simplify_cache,name_quick_cmp> m_simplify_cache;

    optional<result> cache_lookup(expr const & e);
    void cache_save(expr const & e, result const & r);

    /* Basic helpers */
    bool using_eq() { return m_rel == get_eq_name(); }

    bool is_dependent_fn(expr const & f) {
        expr f_type = m_tmp_tctx->whnf(m_tmp_tctx->infer(f));
        lean_assert(is_pi(f_type));
        return has_free_vars(binding_body(f_type));
    }

    /* Results */
    result lift_from_eq(expr const & x, result const & r);
    result join(result const & r1, result const & r2);        
    result funext(result const & r, expr const & l);
    result finalize(result const & r);

    /* Simplification */
    result simplify(expr const & e);    
    result simplify_lambda(expr const & e);
    result simplify_pi(expr const & e);
    result simplify_app(expr const & e);
    result simplify_fun(expr const & e);
    
    /* Rewriting */
    result rewrite(expr const & e);    
    result rewrite(expr const & e, simp_rule const & sr);
    void init_tmp_tctx_for(simp_rule_core const & sr);

    /* Congruence */
    result congr(result const & r_f, result const & r_arg);        
    result congr_fun(result const & r_f, expr const & arg);
    result congr_arg(expr const & f, result const & r_arg);
    result congr_funs(result const & r_f, buffer<expr> const & args);    
    
    result try_congrs(expr const & e);    
    result try_congr(expr const & e, congr_rule const & cr);

public:
    simplifier(branch const & b, name const & rel);
    result operator()(expr const & e) { return simplify(e); }

};

/* Constructor */

simplifier::simplifier(branch const & b, name const & rel):
    m_app_builder(*m_tmp_tctx), m_branch(b), m_rel(rel) { }

/* Cache */
optional<result> simplifier::cache_lookup(expr const & e) {
    simplify_cache & cache = m_simplify_cache[m_rel];
    auto it = cache.find(e);
    if (it != cache.end()) return optional<result>(it->second);
    return optional<result>();
}
void simplifier::cache_save(expr const & e, result const & r) {
    simplify_cache & cache = m_simplify_cache[m_rel];
    cache.insert(mk_pair(e,r));
}


/* Results */

result simplifier::lift_from_eq(expr const & x, result const & r) {
    lean_assert(!r.is_none());

    expr l = m_tmp_tctx->mk_tmp_local(m_tmp_tctx->infer(x));
    auto motive_local = m_app_builder.mk_app(m_rel,x,l);
    lean_assert(motive_local);

    expr motive = Fun(l,*motive_local);
    
    auto Rxx = m_app_builder.mk_refl(m_rel,x);
    lean_assert(Rxx);

    auto pf = m_app_builder.mk_eq_rec(motive,*Rxx,r.get_proof());
    return result(r.get_new(),pf);
}

result simplifier::join(result const & r1, result const & r2) {
    /* Assumes that both results are with respect to the same relation */
    if (r1.is_none()) {
        return r2;
    }
    else if (r2.is_none()) {
        return r1;
    }
    else {
        auto trans = m_app_builder.mk_trans(m_rel,r1.get_proof(),r2.get_proof());
        lean_assert(trans);
        return result(r2.get_new(),*trans);
    }
}

result simplifier::funext(result const & r, expr const & l) {
    // theorem funext {f₁ f₂ : Πx : A, B x} : (∀x, f₁ x = f₂ x) → f₁ = f₂ :=
    lean_assert(!r.is_none());
    expr e = Fun(l,r.get_new());
    if (auto pf = m_app_builder.mk_app(get_funext_name(),Fun(l,r.get_proof())))
        return result(e,*pf);
    else
        throw blast_exception("failed on [funext] matching",e);
}

result simplifier::finalize(result const & r) {
    if (!r.is_none()) return r;
    if (auto pf = m_app_builder.mk_refl(m_rel,r.get_new()))
        return result(r.get_new(),*pf);
    else
        throw blast_exception("failed on [refl] matching",r.get_new());
}

/* Simplification */

result simplifier::simplify(expr const & e) {
    m_num_steps++;
    flet<unsigned> inc_depth(m_depth, m_depth+1);

    if (m_trace) {
        ios().get_diagnostic_channel() << m_num_steps << "." << m_depth << "." << m_rel << ": " << e << "\n";
    }

    if (m_num_steps > m_max_steps)
        throw blast_exception("simplifier failed, maximum number of steps exceeded", e);

    if (m_memoize) {
        if (auto it = cache_lookup(e)) return *it;
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
        /* TODO
        if (m_expand_macros) {
            if (auto m = blast::expand_macro(e)) r = join(r,simplify(whnf(*m)));
        }
        */
        break;
    case expr_kind::Lambda:
        if (using_eq()) r = join(r,simplify_lambda(r.get_new()));
        break;
    case expr_kind::Pi:
        r = join(r,simplify_pi(r.get_new()));
        break;
    case expr_kind::App:
        r = join(r,simplify_app(r.get_new()));
        break;
    }

    if (!m_top_down) r = join(r,rewrite(whnf(r.get_new())));

    if (r.get_new() == e && !using_eq()) {
        {
            flet<name> use_eq(m_rel, get_eq_name());
            r = simplify(r.get_new());
        }
        if (!r.is_none()) r = lift_from_eq(e,r);
    }

    if (m_exhaustive && r.get_new() != e) r = join(r,simplify(r.get_new()));

    if (m_memoize) cache_save(e,r);

    return r;
}
    
result simplifier::simplify_lambda(expr const & _e) {
    lean_assert(is_lambda(_e));
    expr e = _e;
    
    buffer<expr> ls;
    while (is_lambda(e)) {
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = m_tmp_tctx->mk_tmp_local(d,binding_info(e));
        ls.push_back(l);
        e = instantiate(binding_body(e),l);
    }

    result r = simplify(e);
    if (r.is_none()) { return result(_e); }

    for (int i = ls.size() - 1; i >= 0; --i) r = funext(r,ls[i]);

    return r;
}

result simplifier::simplify_pi(expr const & e) {
    lean_assert(is_pi(e));
    return try_congrs(e);
}

result simplifier::simplify_app(expr const & e) {
    lean_assert(is_app(e));
    // TODO simplify operator as well, in cases (1) and (2)
    
    /* (1) Try user-defined congruences */
    result r = try_congrs(e);
    if (!r.is_none()) {
        if (using_eq()) return join(r,simplify_fun(r.get_new()));
        else return r;
    }
    
    /* (2) Synthesize congruence lemma */
    if (using_eq()) {
        // TODO
    }

    /* (3) Fall back on generic binary congruence */
    if (using_eq()) {
        expr const & f = app_fn(e);
        expr const & arg = app_arg(e);

        result r_f = simplify(f);

        if (is_dependent_fn(f)) {
            if (r_f.is_none()) return e;
            else return congr_fun(r_f,arg);
        }
        else {
            result r_arg = simplify(arg);
            if (r_f.is_none() && r_arg.is_none()) return e;
            else if (r_f.is_none()) return congr_arg(f,r_arg);
            else if (r_arg.is_none()) return congr_fun(r_f,arg);            
            else return congr(r_f,r_arg);
        }
    }

    return result(e);
}

result simplifier::simplify_fun(expr const & e) {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    result r_f = simplify(f);
    if (r_f.is_none()) return result(e);
    else return congr_funs(simplify(f),args);
}

/* Rewriting */

result simplifier::rewrite(expr const & e) {
    result r(e);

    /* First, we rewrite with local hypotheses */
    //TODO

    /* Next, we rewrite with the [simp_rule_set] */
    simp_rule_set const * sr = get_simp_rule_sets(env()).find(m_rel);
    if (!sr) return r;

    list<simp_rule> const * srs = sr->find_simp(e);
    if (!srs) return r;

    bool modified = true;
    while (modified) {
        modified = false;
        for_each(*srs,[&](simp_rule const & sr) {
                result r_rew = rewrite(r.get_new(),sr);
                if (r_rew.is_none()) return;
                r = join(r,r_rew);
                modified = true;
            }
            );
    }
    
    return r;
}

result simplifier::rewrite(expr const & e, simp_rule const & sr) {
    blast_tmp_type_context tmp_tctx(sr.get_num_umeta(),sr.get_num_emeta());

    if (!tmp_tctx->is_def_eq(e,sr.get_lhs())) return result(e);

    /* Traverse metavariables backwards */
    for (int i = sr.get_num_emeta() - 1; i >= 0; --i) {
        expr const & m = sr.get_emeta(i);
        bool is_instance = sr.is_instance(i);

        if (is_instance) {
            expr type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));
            if (auto v = tmp_tctx->mk_class_instance(type)) {
                if (!tmp_tctx->force_assign(m, *v))
                    return result(e);
            } else {
                return result(e);
            }
        }

        if (tmp_tctx->is_mvar_assigned(i)) continue;

        if (tmp_tctx->is_prop(tmp_tctx->infer(m))) {
            // TODO try to prove
            return result(e);
        }

        /* We fail if there is a meta variable that we still cannot assign */
        return result(e);
    }

    for (unsigned i = 0; i < sr.get_num_umeta(); i++) {
        if (!tmp_tctx->is_uvar_assigned(i)) return result(e);
    }
    
    expr e_s = tmp_tctx->instantiate_uvars_mvars(sr.get_rhs());

    if (sr.is_perm() && !is_lt(e_s,e,false)) return result(e);
    expr pf = tmp_tctx->instantiate_uvars_mvars(sr.get_proof());
    return result(result(e_s,pf));
}



/* Congruence */
result simplifier::congr(result const & r_f, result const & r_arg) {
    lean_assert(!r_f.is_none() && !r_arg.is_none());
    // theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
    expr e = mk_app(r_f.get_new(),r_arg.get_new());
    if (auto pf = m_app_builder.mk_app(get_congr_name(),r_f.get_proof(),r_arg.get_proof()))
        return result(e,*pf);
    else
        throw blast_exception("failed on [congr] matching",e);
}

result simplifier::congr_fun(result const & r_f, expr const & arg) {
    lean_assert(!r_f.is_none());
    // theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
    expr e = mk_app(r_f.get_new(),arg);
    if (auto pf = m_app_builder.mk_app(get_congr_fun_name(),r_f.get_proof(),arg))
        return result(e,*pf);
    else
        throw blast_exception("failed on [congr_fun] matching",e);        
}

result simplifier::congr_arg(expr const & f, result const & r_arg) {
    lean_assert(!r_arg.is_none());
    // theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂
    expr e = mk_app(f,r_arg.get_new());
    if (auto pf = m_app_builder.mk_app(get_congr_arg_name(),f,r_arg.get_proof()))
        return result(e,*pf);
    else
        throw blast_exception("failed on [congr_arg] matching",e);                
}

result simplifier::congr_funs(result const & r_f, buffer<expr> const & args) {
    lean_assert(!r_f.is_none());
    // congr_fun : ∀ {A : Type} {B : A → Type} {f g : Π (x : A), B x}, f = g → (∀ (a : A), f a = g a)
    expr e = r_f.get_new();
    expr pf = r_f.get_proof();
    for (unsigned i = 0; i < args.size(); ++i) {
        e = mk_app(e,args[i]);
        auto p = m_app_builder.mk_app(get_congr_fun_name(),pf,args[i]);
        if (p) pf = *p;
        else throw blast_exception("failed on [congr_fun] matching",e);
    }
    return result(e,pf);
}

result simplifier::try_congrs(expr const & e) {
    simp_rule_set const * sr = get_simp_rule_sets(env()).find(m_rel);
    if (!sr) return result(e);

    list<congr_rule> const * crs = sr->find_congr(e);
    if (!crs) return result(e);

    result r(e);
    for_each(*crs,[&](congr_rule const & cr) {
            if (!r.is_none()) return;
            r = try_congr(e,cr);
        }); 
    return r;
}

result simplifier::try_congr(expr const & e, congr_rule const & cr) {
    blast_tmp_type_context tmp_tctx(cr.get_num_umeta(),cr.get_num_emeta());

    if (!tmp_tctx->is_def_eq(e,cr.get_lhs())) return result(e);
    
    /* First, iterate over the congruence hypotheses */
    bool failed = false;
    bool simplified = false;
    list<expr> const & congr_hyps = cr.get_congr_hyps();
    for_each(congr_hyps,[&](expr const & m) {
        if (failed) return;
        buffer<expr> ls;
        expr m_type = tmp_tctx->infer(m);

        while (is_pi(m_type)) {
            expr d = instantiate_rev(binding_domain(m_type), ls.size(), ls.data());
            expr l = tmp_tctx->mk_tmp_local(d,binding_info(e));
            ls.push_back(l);
            m_type = instantiate(binding_body(m_type),l);
        }

        expr h_rel, h_lhs, h_rhs;
        bool valid = is_simp_relation(env(), m_type, h_rel, h_lhs, h_rhs) && is_constant(h_rel);
        lean_assert(valid);
        {
            flet<name> set_name(m_rel,const_name(h_rel));
            flet<list<expr>> set_local_ctx(m_local_ctx,to_list(ls));
            h_lhs = tmp_tctx->instantiate_uvars_mvars(h_lhs);
            result r_congr_hyp = simplify(h_lhs);
            expr hyp;
            if (r_congr_hyp.is_none()) {
                hyp = finalize(r_congr_hyp).get_proof();
            }
            else {
                hyp = r_congr_hyp.get_proof();
                simplified = true;
            }
            hyp = Fun(ls,hyp);
            if (!tmp_tctx->is_def_eq(m,hyp)) failed = true;
        }
        });
    if (failed || !simplified) return result(e);
    /* Traverse metavariables backwards, proving or synthesizing the rest */
    for (int i = cr.get_num_emeta() - 1; i >= 0; --i) {
        expr const & m = cr.get_emeta(i);
        bool is_instance = cr.is_instance(i);

        if (is_instance) {
            expr type = tmp_tctx->instantiate_uvars_mvars(tmp_tctx->infer(m));
            if (auto v = tmp_tctx->mk_class_instance(type)) {
                if (!tmp_tctx->force_assign(m, *v))
                    return result(e);
            } else {
                return result(e);
            }
        }

        if (tmp_tctx->is_mvar_assigned(i)) continue;

        if (tmp_tctx->is_prop(tmp_tctx->infer(m))) {
            // TODO try to prove
            return result(e);
        }

        /* We fail if there is a meta variable that we still cannot assign */
        return result(e);
    }

    for (unsigned i = 0; i < cr.get_num_umeta(); i++) {
        if (!tmp_tctx->is_uvar_assigned(i)) return result(e);
    }

    expr e_s = tmp_tctx->instantiate_uvars_mvars(cr.get_rhs());
    expr pf = tmp_tctx->instantiate_uvars_mvars(cr.get_proof());
    return result(e_s,pf);
}

/* Setup and teardown */

void initialize_simplifier() {
    g_simplify_max_steps     = new name{"simplify", "max_steps"};
    g_simplify_top_down      = new name{"simplify", "top_down"};
    g_simplify_exhaustive    = new name{"simplify", "exhaustive"};
    g_simplify_memoize       = new name{"simplify", "memoize"};
    g_simplify_contextual    = new name{"simplify", "contextual"};
    g_simplify_expand_macros = new name{"simplify", "expand_macros"};
    g_simplify_trace         = new name{"simplify", "trace"};    

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
    

}

void finalize_simplifier() {
    delete g_simplify_trace;
    delete g_simplify_expand_macros;
    delete g_simplify_contextual;
    delete g_simplify_memoize;
    delete g_simplify_exhaustive;
    delete g_simplify_top_down;    
    delete g_simplify_max_steps;
}

/* Entry point */

result simplify(branch const & b, name const & rel, expr const & e) {
    return simplifier(b,rel)(e);
}

}}
