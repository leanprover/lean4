/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "kernel/free_vars.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"

namespace lean {
template<bool ClosedSubst>
expr instantiate_core(expr const & a, unsigned s, unsigned n, expr const * subst) {
    return replace(a, [=](expr const & m, unsigned offset) -> expr {
            if (is_var(m)) {
                unsigned vidx = var_idx(m);
                if (vidx >= offset + s) {
                    if (vidx < offset + s + n) {
                        if (ClosedSubst)
                            return subst[vidx - s - offset];
                        else
                            return lift_free_vars(subst[vidx - s - offset], offset);
                    } else {
                        return mk_var(vidx - n);
                    }
                } else {
                    return m;
                }
            } else {
                return m;
            }
        });
}

expr instantiate_with_closed(expr const & e, unsigned s, unsigned n, expr const * subst) { return instantiate_core<true>(e, s, n, subst); }
expr instantiate_with_closed(expr const & e, unsigned n, expr const * s) { return instantiate_with_closed(e, 0, n, s); }
expr instantiate_with_closed(expr const & e, std::initializer_list<expr> const & l) { return instantiate_with_closed(e, l.size(), l.begin()); }
expr instantiate_with_closed(expr const & e, expr const & s) { return instantiate_with_closed(e, 1, &s); }
expr instantiate(expr const & e, unsigned s, unsigned n, expr const * subst) { return instantiate_core<false>(e, s, n, subst); }
expr instantiate(expr const & e, unsigned n, expr const * s) { return instantiate(e, 0, n, s); }
expr instantiate(expr const & e, std::initializer_list<expr> const & l) {  return instantiate(e, l.size(), l.begin()); }
expr instantiate(expr const & e, unsigned i, expr const & s) { return instantiate(e, i, 1, &s); }
expr instantiate(expr const & e, expr const & s) { return instantiate(e, 0, s); }

bool is_head_beta(expr const & t) {
    expr const * it = &t;
    while (is_app(*it)) {
        expr const & f = app_fn(*it);
        if (is_lambda(f)) {
            return true;
        } else if (is_app(f)) {
            it = &f;
        } else {
            return false;
        }
    }
    return false;
}

expr apply_beta(expr f, unsigned num_args, expr const * args) {
    lean_assert(num_args > 0);
    if (!is_lambda(f)) {
        return mk_rev_app(f, num_args, args);
    } else {
        unsigned m = 1;
        while (is_lambda(binder_body(f)) && m < num_args) {
            f = binder_body(f);
            m++;
        }
        lean_assert(m <= num_args);
        return mk_rev_app(instantiate(binder_body(f), m, args + (num_args - m)), num_args - m, args);
    }
}

expr head_beta_reduce(expr const & t) {
    if (!is_head_beta(t)) {
        return t;
    } else {
        buffer<expr> args;
        expr const * it = &t;
        while (true) {
            lean_assert(is_app(*it));
            expr const & f = app_fn(*it);
            args.push_back(app_arg(*it));
            if (is_lambda(f)) {
                return apply_beta(f, args.size(), args.data());
            } else {
                lean_assert(is_app(f));
                it = &f;
            }
        }
    }
}

expr beta_reduce(expr t) {
    auto f = [=](expr const & m, unsigned) -> expr {
        if (is_head_beta(m))
            return head_beta_reduce(m);
        else
            return m;
    };
    while (true) {
        expr new_t = replace_fn(f)(t);
        if (new_t == t)
            return new_t;
        else
            t = new_t;
    }
}
}
