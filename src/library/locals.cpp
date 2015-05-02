/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_set.h"
#include "kernel/expr.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "library/locals.h"

namespace lean {
void collect_univ_params_core(level const & l, name_set & r) {
    for_each(l, [&](level const & l) {
            if (!has_param(l))
                return false;
            if (is_param(l))
                r.insert(param_id(l));
            return true;
        });
}

name_set collect_univ_params(expr const & e, name_set const & ls) {
    if (!has_param_univ(e)) {
        return ls;
    } else {
        name_set r = ls;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_param_univ(e)) {
                    return false;
                } else if (is_sort(e)) {
                    collect_univ_params_core(sort_level(e), r);
                } else if (is_constant(e)) {
                    for (auto const & l : const_levels(e))
                        collect_univ_params_core(l, r);
                }
                return true;
            });
        return r;
    }
}

level_param_names to_level_param_names(name_set const & ls) {
    level_param_names r;
    ls.for_each([&](name const & n) {
            r = level_param_names(n, r);
        });
    return r;
}

void collect_locals(expr const & e, expr_struct_set & ls, bool restricted) {
    if (!has_local(e))
        return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_local(e))
                return false;
            if (is_local(e)) {
                ls.insert(e);
                return !restricted; // search type if not restricted
            }
            if (is_meta(e))
                return !restricted; // search type if not restricted
            return true;
        });
}

bool contains_local(expr const & e, name const & n) {
    if (!has_local(e))
        return false;
    bool result = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (result || !has_local(e))  {
                return false;
            } else if (is_local(e) && mlocal_name(e) == n) {
                result = true;
                return false;
            } else {
                return true;
            }
        });
    return result;
}

optional<expr> depends_on(unsigned sz, expr const * es, expr const & h) {
    for (unsigned i = 0; i < sz; i++)
        if (depends_on(es[i], h))
            return some_expr(es[i]);
    return none_expr();
}
}
