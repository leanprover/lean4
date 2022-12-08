/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include <vector>
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {
expr abstract(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_fvar(e); }));
    if (!has_fvar(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m))
                return some_expr(m); // expression m does not contain free variables
            if (is_fvar(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (fvar_name(subst[i]) == fvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        });
}

expr abstract(expr const & e, name const & n) {
    expr fvar = mk_fvar(n);
    return abstract(e, 1, &fvar);
}

static object * lean_expr_abstract_core(object * e0, size_t n, object * subst) {
    lean_assert(n <= lean_array_size(subst));
    expr const & e = reinterpret_cast<expr const &>(e0);
    if (!has_fvar(e) && !has_mvar(e)) {
        lean_inc(e0);
        return e0;
    }
    expr r = replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m) && !has_mvar(m))
                return some_expr(m); // expression m does not contain free/meta variables
            bool fv = is_fvar(m);
            bool mv = is_mvar(m);
            if (fv || mv) {
                size_t i = n;
                while (i > 0) {
                    --i;
                    object * v = lean_array_get_core(subst, i);
                    if (fv && is_fvar_core(v) && fvar_name_core(v) == fvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                    if (mv && is_mvar_core(v) && mvar_name_core(v) == mvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        });
    return r.steal();
}

extern "C" LEAN_EXPORT object * lean_expr_abstract_range(object * e, object * n, object * subst) {
    if (!lean_is_scalar(n))
        return lean_expr_abstract_core(e, lean_array_size(subst), subst);
    else
        return lean_expr_abstract_core(e, std::min(lean_unbox(n), lean_array_size(subst)), subst);
}

extern "C" LEAN_EXPORT object * lean_expr_abstract(object * e, object * subst) {
    return lean_expr_abstract_core(e, lean_array_size(subst), subst);
}
}
