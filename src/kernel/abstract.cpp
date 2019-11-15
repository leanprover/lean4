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
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_local_or_fvar(e); }));
    if (!has_fvar(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m))
                return some_expr(m); // expression m does not contain free variables
            if (is_local_or_fvar(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (local_or_fvar_name(subst[i]) == local_or_fvar_name(m))
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
    if (!has_fvar(e)) {
        lean_inc(e0);
        return e0;
    }
    expr r = replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m))
                return some_expr(m); // expression m does not contain free variables
            if (is_fvar(m)) {
                size_t i = n;
                while (i > 0) {
                    --i;
                    object * v = lean_array_get_core(subst, i);
                    if (is_fvar_core(v) && fvar_name_core(v) == fvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        });
    return r.steal();
}

extern "C" object * lean_expr_abstract_range(object * e, object * n, object * subst) {
    if (!lean_is_scalar(n))
        return lean_expr_abstract_core(e, lean_array_size(subst), subst);
    else
        return lean_expr_abstract_core(e, std::min(lean_unbox(n), lean_array_size(subst)), subst);
}

extern "C" object * lean_expr_abstract(object * e, object * subst) {
    return lean_expr_abstract_core(e, lean_array_size(subst), subst);
}

/* ------ LEGACY CODE -------------
   The following API is to support legacy
   code where the type of a local constant (aka free variable)
   was stored in the local constant itself.
   This approach was used in Lean2, and is being abandoned in Lean4.

   TODO(Leo): delete */

template<bool is_lambda>
expr mk_binding(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract(local_type(l), i, locals);
        if (is_lambda)
            r = mk_lambda(local_pp_name(l), t, r, local_info(l));
        else
            r = mk_pi(local_pp_name(l), t, r, local_info(l));
    }
    return r;
}

expr Pi(unsigned num, expr const * locals, expr const & b) { return mk_binding<false>(num, locals, b); }
expr Fun(unsigned num, expr const * locals, expr const & b) { return mk_binding<true>(num, locals, b); }
}
