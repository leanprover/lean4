/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include <vector>
#include "expr.h"
#include "expr_functors.h"

namespace lean {
namespace max_shared_ns {
struct expr_struct_eq { unsigned operator()(expr const & e1, expr const & e2) const { return e1 == e2; }};
typedef typename std::unordered_set<expr, expr_hash, expr_struct_eq> expr_cache;
static thread_local expr_cache g_cache;
expr apply(expr const & a) {
    auto r = g_cache.find(a);
    if (r != g_cache.end())
        return *r;
    switch (a.kind()) {
    case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
        g_cache.insert(a);
        return a;
    case expr_kind::App: {
        std::vector<expr> new_args;
        bool modified = false;
        for (expr const & old_arg : app_args(a)) {
            new_args.push_back(apply(old_arg));
            if (!eqp(old_arg, new_args.back()))
                modified = true;
        }
        if (!modified) {
            g_cache.insert(a);
            return a;
        }
        else {
            expr r = app(static_cast<unsigned>(new_args.size()), new_args.data());
            g_cache.insert(r);
            return r;
        }
    }
    case expr_kind::Lambda:
    case expr_kind::Pi: {
        expr const & old_t = get_abs_type(a);
        expr const & old_e = get_abs_expr(a);
        expr t = apply(old_t);
        expr e = apply(old_e);
        if (!eqp(t, old_t) || !eqp(e, old_e)) {
            name const & n     = get_abs_name(a);
            expr r = is_pi(a) ? pi(n, t, e) : lambda(n, t, e);
            g_cache.insert(r);
            return r;
        }
        else {
            g_cache.insert(a);
            return a;
        }
    }}
    lean_unreachable();
    return a;
}
} // namespace max_shared_ns
expr max_shared(expr const & a) {
    max_shared_ns::g_cache.clear();
    expr r = max_shared_ns::apply(a);
    max_shared_ns::g_cache.clear();
    return r;
}
} // namespace lean
