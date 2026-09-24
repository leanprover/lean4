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

class replace_rec_fn {
    struct key_hasher {
        std::size_t operator()(std::pair<lean_object *, unsigned> const & p) const {
            return hash((size_t)p.first >> 3, p.second);
        }
    };
    lean::unordered_map<std::pair<lean_object *, unsigned>, expr, key_hasher> m_cache;
    std::function<optional<expr>(expr const &, unsigned)> m_f;
    bool                                                  m_use_cache;

    // `std::unordered_map` keeps element references stable across rehash, so the
    // `slot` pointer obtained on descent remains valid after recursive inserts.
    expr save_result(expr r, expr * slot) {
        if (slot) *slot = r;
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        expr * slot = nullptr;
        if (m_use_cache && !is_likely_unshared(e)) {
            auto p = m_cache.try_emplace(mk_pair(e.raw(), offset));
            if (!p.second)
                return p.first->second;
            slot = &p.first->second;
        }
        if (optional<expr> r = m_f(e, offset)) {
            return save_result(std::move(*r), slot);
        } else {
            switch (e.kind()) {
            case expr_kind::Const: case expr_kind::Sort:
            case expr_kind::BVar:  case expr_kind::Lit:
            case expr_kind::MVar:  case expr_kind::FVar:
                return save_result(e, slot);
            case expr_kind::MData: {
                expr new_e = apply(mdata_expr(e), offset);
                return save_result(update_mdata(e, new_e), slot);
            }
            case expr_kind::Proj: {
                expr new_e = apply(proj_expr(e), offset);
                return save_result(update_proj(e, new_e), slot);
            }
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(update_app(e, new_f, new_a), slot);
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                expr new_d = apply(binding_domain(e), offset);
                expr new_b = apply(binding_body(e), offset+1);
                return save_result(update_binding(e, new_d, new_b), slot);
            }
            case expr_kind::Let: {
                expr new_t = apply(let_type(e), offset);
                expr new_v = apply(let_value(e), offset);
                expr new_b = apply(let_body(e), offset+1);
                return save_result(update_let(e, new_t, new_v, new_b), slot);
            }
            }
            lean_unreachable();
        }
    }
public:
    template<typename F>
    replace_rec_fn(F const & f, bool use_cache):m_f(f), m_use_cache(use_cache) {
    }

    expr operator()(expr const & e) { return apply(e, 0); }
};

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache) {
    return replace_rec_fn(f, use_cache)(e);
}

class replace_fn {
    lean::unordered_map<lean_object *, expr> m_cache;
    lean_object * m_f;

    // `std::unordered_map` keeps element references stable across rehash, so the
    // `slot` pointer obtained on descent remains valid after recursive inserts.
    expr save_result(expr const & r, expr * slot) {
        if (slot) *slot = r;
        return r;
    }

    expr apply(expr const & e) {
        expr * slot = nullptr;
        if (is_shared(e)) {
            auto p = m_cache.try_emplace(e.raw());
            if (!p.second)
                return p.first->second;
            slot = &p.first->second;
        }

        lean_inc(e.raw());
        lean_inc_ref(m_f);
        lean_object * r = lean_apply_1(m_f, e.raw());
        if (!lean_is_scalar(r)) {
            expr e_new(lean_ctor_get(r, 0), true);
            lean_dec_ref(r);
            return save_result(e_new, slot);
        }

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return save_result(e, slot);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e));
            return save_result(update_mdata(e, new_e), slot);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e));
            return save_result(update_proj(e, new_e), slot);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e));
            expr new_a = apply(app_arg(e));
            return save_result(update_app(e, new_f, new_a), slot);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e));
            expr new_b = apply(binding_body(e));
            return save_result(update_binding(e, new_d, new_b), slot);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e));
            expr new_v = apply(let_value(e));
            expr new_b = apply(let_body(e));
            return save_result(update_let(e, new_t, new_v, new_b), slot);
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
}
