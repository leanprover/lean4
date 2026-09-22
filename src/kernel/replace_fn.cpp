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

// Out-of-line `std::function`-typed overloads, declared in replace_fn.h. Defer
// to the templated implementation in the header, instantiated once per
// `std::function` shape. Hot callers should bypass these and use the templated
// `replace<F>` (or `replace<Skip, F>`) directly to avoid the per-call indirect
// dispatch through `std::function`.
expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache) {
    return replace_rec_fn<std::function<optional<expr>(expr const &, unsigned)>>(f, use_cache)(e);
}

expr replace(expr const & e,
             std::function<bool(expr const &, unsigned)> const & skip,
             std::function<optional<expr>(expr const &, unsigned)> const & f,
             bool use_cache) {
    using F = std::function<optional<expr>(expr const &, unsigned)>;
    using S = std::function<bool(expr const &, unsigned)>;
    return replace_rec_fn<F, S>(skip, f, use_cache)(e);
}

class replace_fn {
    lean::unordered_map<lean_object *, expr> m_cache;
    lean_object * m_f;

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(mk_pair(e.raw(), r));
        return r;
    }

    expr apply(expr const & e) {
        bool shared = false;
        if (is_shared(e)) {
            auto it = m_cache.find(e.raw());
            if (it != m_cache.end())
                return it->second;
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
}
