/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <utility>
#include <unordered_map>
#include "kernel/replace_fn.h"
#include "util/alloc.h"

namespace lean {

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache) {
    return replace_tpl(e, f, use_cache);
}

class replace_fn {
    replace_cache m_cache;
    lean_object * m_f;

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), 0, r);
        return r;
    }

    expr apply(expr const & e) {
        bool shared = false;
        if (is_shared(e)) {
            if (lean_object * r = m_cache.find(e.raw()))
                return expr(r, true);
            shared = true;
        }

        lean_inc(e.raw());
        lean_inc_ref(m_f);
        lean_object * r = lean_apply_1(m_f, e.raw());
        if (!lean_is_scalar(r)) {
            expr e_new(lean_ctor_get(r, 0), true);
            lean_dec_ref(r);
            return save_result(e, e_new, shared);
        }

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return save_result(e, e, shared);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e));
            return save_result(e, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e));
            return save_result(e, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e));
            expr new_a = apply(app_arg(e));
            return save_result(e, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e));
            expr new_b = apply(binding_body(e));
            return save_result(e, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e));
            expr new_v = apply(let_value(e));
            expr new_b = apply(let_body(e));
            return save_result(e, update_let(e, new_t, new_v, new_b), shared);
        }}
        lean_unreachable();
    }
public:
    replace_fn(lean_object * f):m_f(f) {}
    expr operator()(expr const & e) { return apply(e); }
};

extern "C" LEAN_EXPORT obj_res lean_replace_expr(b_obj_arg f, b_obj_arg e) {
    expr r = replace_fn(f)(TO_REF(expr, e));
    return r.steal();
}

extern "C" object * lean_level_instantiate_params(obj_arg u, obj_arg ps, obj_arg us);

/* `Expr.instantiateLevelParams`: `replace_fn` with `Expr.instantiateLevelParamsCore.replaceFn`
   inlined, so that the traversal and the result are the same as with `Expr.replace`. Levels are
   instantiated by `Level.instantiateParams`. */
class instantiate_level_params_fn {
    replace_cache m_cache;
    b_obj_arg m_ps;
    b_obj_arg m_us;

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), 0, r);
        return r;
    }

    level instantiate(level const & l) {
        // `Level.instantiateParams` returns a level without parameters unchanged and replaces a
        // parameter by its `getParamSubst` value, so only the remaining levels need the call
        if (!has_param(l))
            return l;
        if (is_param(l)) {
            b_obj_arg ps = m_ps;
            b_obj_arg us = m_us;
            while (!lean_is_scalar(ps) && !lean_is_scalar(us)) {
                if (lean_name_eq(lean_ctor_get(ps, 0), param_id(l).raw()))
                    return level(lean_ctor_get(us, 0), true);
                ps = lean_ctor_get(ps, 1);
                us = lean_ctor_get(us, 1);
            }
            return l;
        }
        lean_inc(m_ps);
        lean_inc(m_us);
        return level(lean_level_instantiate_params(l.to_obj_arg(), m_ps, m_us));
    }

    // Keep the level buffer out of the recursive traversal's stack frame.
    __attribute__((noinline))
    expr instantiate_const(expr const & e) {
        buffer<level> new_ls;
        bool same = true;
        for (level const & l : const_levels(e)) {
            level new_l = instantiate(l);
            same = same && is_eqp(new_l, l);
            new_ls.push_back(new_l);
        }
        return same ? e : mk_constant(const_name(e), levels(new_ls));
    }

    expr apply(expr const & e) {
        // cheaper than consulting the cache
        if (!has_param_univ(e))
            return e;

        bool shared = false;
        if (is_shared(e)) {
            if (lean_object * r = m_cache.find(e.raw()))
                return expr(r, true);
            shared = true;
        }

        switch (e.kind()) {
        case expr_kind::Const:
            return save_result(e, instantiate_const(e), shared);
        case expr_kind::Sort: {
            level new_l = instantiate(sort_level(e));
            return save_result(e, is_eqp(new_l, sort_level(e)) ? e : mk_sort(new_l), shared);
        }
        case expr_kind::BVar: case expr_kind::Lit:
        case expr_kind::MVar: case expr_kind::FVar:
            return save_result(e, e, shared);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e));
            return save_result(e, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e));
            return save_result(e, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e));
            expr new_a = apply(app_arg(e));
            return save_result(e, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e));
            expr new_b = apply(binding_body(e));
            return save_result(e, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e));
            expr new_v = apply(let_value(e));
            expr new_b = apply(let_body(e));
            return save_result(e, update_let(e, new_t, new_v, new_b), shared);
        }}
        lean_unreachable();
    }
public:
    instantiate_level_params_fn(b_obj_arg ps, b_obj_arg us):m_ps(ps), m_us(us) {}
    expr operator()(expr const & e) { return apply(e); }
};

/* instantiateLevelParamsImpl (e : @& Expr) (paramNames : @& List Name) (lvls : @& List Level) : Expr */
extern "C" LEAN_EXPORT obj_res lean_expr_instantiate_level_params(b_obj_arg e, b_obj_arg ps, b_obj_arg us) {
    expr r = instantiate_level_params_fn(ps, us)(TO_REF(expr, e));
    return r.steal();
}
}
