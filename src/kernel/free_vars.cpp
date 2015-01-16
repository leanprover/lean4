/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "kernel/free_vars.h"
#include "kernel/expr_sets.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"

namespace lean {
bool has_free_var(expr const & e, unsigned i) {
    bool found = false;
    for_each(e, [&](expr const & e, unsigned offset) {
            if (found)
                return false; // already found
            unsigned n_i = i + offset;
            if (n_i < i)
                return false; // overflow, vidx can't be >= max unsigned
            if (n_i >= get_free_var_range(e))
                return false; // expression e does not contain free variables with idx >= n_i
            if (is_var(e)) {
                unsigned vidx = var_idx(e);
                if (vidx == n_i)
                    found = true;
            }
            return true; // continue search
        });
    return found;
}

expr lower_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_free_var_range(e))
        return e;
    lean_assert(s >= d);
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_free_var_range(e))
                return some_expr(e); // expression e does not contain free variables with idx >= s1
            if (is_var(e) && var_idx(e) >= s1) {
                lean_assert(var_idx(e) >= offset + d);
                return some_expr(mk_var(var_idx(e) - d));
            } else {
                return none_expr();
            }
        });
}
expr lower_free_vars(expr const & e, unsigned d) { return lower_free_vars(e, d, d); }

expr lift_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_free_var_range(e))
        return e;
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_free_var_range(e))
                return some_expr(e); // expression e does not contain free variables with idx >= s1
            if (is_var(e) && var_idx(e) >= s + offset) {
                unsigned new_idx = var_idx(e) + d;
                if (new_idx < var_idx(e))
                    throw exception("invalid lift_free_vars operation, index overflow");
                return some_expr(mk_var(new_idx));
            } else {
                return none_expr();
            }
        });
}
expr lift_free_vars(expr const & e, unsigned d) { return lift_free_vars(e, 0, d); }
}
