/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace.h"
#include "kernel/for_each.h"
#include "kernel/environment.h"
#include "kernel/occurs.h"
#include "library/update_expr.h"
#include "library/printer.h"
#include "library/metavar.h"

namespace lean {
static name g_placeholder_name("_");
static name g_metavar_prefix(name(name(name(0u), "library"), "metavar"));
static name g_subst_prefix(name(name(name(0u), "library"), "subst"));
static name g_lift_prefix(name(name(name(0u), "library"), "lift"));
static name g_lower_prefix(name(name(name(0u), "library"), "lower"));

expr mk_placholder() {
    return mk_constant(g_placeholder_name);
}

bool is_placeholder(expr const & e) {
    return is_constant(e) && const_name(e) == g_placeholder_name;
}

bool has_placeholder(expr const & e) {
    return occurs(mk_placholder(), e);
}

expr mk_metavar(unsigned idx) {
    return mk_constant(name(g_metavar_prefix, idx));
}

bool is_metavar(expr const & n) {
    return is_constant(n) && !const_name(n).is_atomic() && const_name(n).get_prefix() == g_metavar_prefix;
}

unsigned metavar_idx(expr const & n) {
    lean_assert(is_metavar(n));
    return const_name(n).get_numeral();
}

struct found_metavar {};

bool has_metavar(expr const & e) {
    auto f = [](expr const & c, unsigned offset) {
        if (is_metavar(c))
            throw found_metavar();
    };
    try {
        for_each_fn<decltype(f)> proc(f);
        proc(e);
        return false;
    } catch (found_metavar) {
        return true;
    }
}

bool has_metavar(expr const & e, unsigned midx) {
    auto f = [=](expr const & m, unsigned offset) {
        if (is_metavar(m) && metavar_idx(m) == midx)
            throw found_metavar();
    };
    try {
        for_each_fn<decltype(f)> proc(f);
        proc(e);
        return false;
    } catch (found_metavar) {
        return true;
    }
}

expr mk_subst_fn(unsigned idx) {
    return mk_constant(name(g_subst_prefix, idx));
}

bool is_subst_fn(expr const & n) {
    return is_constant(n) && !const_name(n).is_atomic() && const_name(n).get_prefix() == g_subst_prefix;
}

expr mk_subst(expr const & e, unsigned i, expr const & c) {
    unsigned s, n;
    expr a;
    if (is_lift(e, a, s, n) && s <= i && i < s+n) {
        return e;
    } else {
        return mk_eq(mk_subst_fn(i), mk_eq(e, c));
    }
}

bool is_subst(expr const & e, expr & c, unsigned & i, expr & v) {
    if (is_eq(e) && is_subst_fn(eq_lhs(e))) {
        i = const_name(eq_lhs(e)).get_numeral();
        c = eq_lhs(eq_rhs(e));
        v = eq_rhs(eq_rhs(e));
        return true;
    } else {
        return false;
    }
}

bool is_subst(expr const & e) {
    return is_eq(e) && is_subst_fn(eq_lhs(e));
}

expr mk_lift_fn(unsigned s, unsigned n) {
    lean_assert(n > 0);
    return mk_constant(name(name(g_lift_prefix, s), n));
}

bool is_lift_fn(expr const & n) {
    return
        is_constant(n) &&
        !const_name(n).is_atomic() &&
        !const_name(n).get_prefix().is_atomic() &&
        const_name(n).get_prefix().get_prefix() == g_lift_prefix;
}

expr mk_lift(expr const & e, unsigned s, unsigned n) {
    return mk_eq(mk_lift_fn(s, n), e);
}

bool is_lift(expr const & e, expr & c, unsigned & s, unsigned & n) {
    if (is_eq(e) && is_lift_fn(eq_lhs(e))) {
        name const & l = const_name(eq_lhs(e));
        c = eq_rhs(e);
        n = l.get_numeral();
        s = l.get_prefix().get_numeral();
        return true;
    } else {
        return false;
    }
}

bool is_lift(expr const & e) {
    return is_eq(e) && is_lift_fn(eq_lhs(e));
}

expr mk_lower_fn(unsigned s, unsigned n) {
    return mk_constant(name(name(g_lower_prefix, s), n));
}

bool is_lower_fn(expr const & n) {
    return
        is_constant(n) &&
        !const_name(n).is_atomic() &&
        !const_name(n).get_prefix().is_atomic() &&
        const_name(n).get_prefix().get_prefix() == g_lower_prefix;
}

expr mk_lower(expr const & e, unsigned s2, unsigned n2) {
    unsigned s1, n1;
    expr c;
    if (is_lift(e, c, s1, n1) && s1 <= s2 - n2 && s2 <= s1 + n1) {
        n1 -= n2;
        if (n1 == 0)
            return c;
        else
            return mk_lift(c, s1, n1);
    } else {
        return mk_eq(mk_lower_fn(s2, n2), e);
    }
}

bool is_lower(expr const & e, expr & c, unsigned & s, unsigned & n) {
    if (is_eq(e) && is_lower_fn(eq_lhs(e))) {
        name const & l = const_name(eq_lhs(e));
        c = eq_rhs(e);
        n = l.get_numeral();
        s = l.get_prefix().get_numeral();
        return true;
    } else {
        return false;
    }
}

bool is_lower(expr const & e) {
    return is_eq(e) && is_lower_fn(eq_lhs(e));
}

bool is_meta(expr const & e) {
    return is_metavar(e) || is_subst(e) || is_lift(e) || is_lower(e);
}

expr lower_free_vars_mmv(expr const & a, unsigned s, unsigned n) {
    if (n == 0)
        return a;
    lean_assert(s >= n);
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= s + offset) {
            return mk_var(var_idx(e) - n);
        } else if (is_meta(e)) {
            return mk_lower(e, s + offset, n);
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}

expr lift_free_vars_mmv(expr const & a, unsigned s, unsigned n) {
    if (n == 0)
        return a;
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= s + offset) {
            return mk_var(var_idx(e) + n);
        } else if (is_meta(e)) {
            return mk_lift(e, s + offset, n);
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}

expr instantiate_free_var_mmv(expr const & a, unsigned i, expr const & c) {
    auto f = [&](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx == offset + i)
                return lift_free_vars_mmv(c, 0, offset);
            else if (vidx > offset + i)
                return mk_var(vidx - 1);
            else
                return e;
        } else if (is_meta(e)) {
            return mk_lower(mk_subst(e, offset, lift_free_vars_mmv(c, 0, offset+1)), offset+1, 1);
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}

expr subst_mmv(expr const & a, unsigned i, expr const & c) {
    auto f = [&](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx == offset + i)
                return lift_free_vars_mmv(c, 0, offset);
            else
                return e;
        } else if (is_meta(e)) {
            return mk_subst(e, offset, lift_free_vars_mmv(c, 0, offset));
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}

expr get_metavar(expr const & e) {
    lean_assert(is_meta(e));
    if (is_metavar(e)) {
        return e;
    } else {
        unsigned i, s, n;
        expr c, v;
        if (is_lift(e, c, s, n)) {
            return get_metavar(c);
        } else if (is_lower(e, c, s, n)) {
            return get_metavar(c);
        } else if (is_subst(e, c, i, v)) {
            return get_metavar(c);
        } else {
            lean_unreachable();
            return e;
        }
    }
}

expr instantiate_metavar_core(expr const & e, expr const & v) {
    lean_assert(is_meta(e));
    unsigned i, s, n;
    expr c, a;
    if (is_metavar(e)) {
        return v;
    } else if (is_subst(e, c, i, a)) {
        return subst_mmv(instantiate_metavar_core(c, v), i, a);
    } else if (is_lift(e, c, s, n)) {
        return lift_free_vars_mmv(instantiate_metavar_core(c, v), s, n);
    } else if (is_lower(e, c, s, n)) {
        return lower_free_vars_mmv(instantiate_metavar_core(c, v), s, n);
    } else {
        lean_unreachable();
        return e;
    }
}

expr instantiate_metavar(expr const & a, unsigned midx, expr const & v) {
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_meta(e)) {
            expr m = get_metavar(e);
            lean_assert(is_metavar(m));
            if (metavar_idx(m) == midx) {
                return instantiate_metavar_core(e, v);
            } else {
                return e;
            }
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}

static expr get_def_value(name const & n, environment const & env, name_set const * defs) {
    if (defs == nullptr || defs->find(n) != defs->end()) {
        object const & obj = env.find_object(n);
        if (obj && obj.is_definition() && !obj.is_opaque())
            return obj.get_value();
    }
    return expr();
}

expr head_reduce_mmv(expr const & e, environment const & env, name_set const * defs) {
    if (is_app(e) && is_lambda(arg(e, 0))) {
        expr r = arg(e, 0);
        unsigned num = num_args(e);
        unsigned i = 1;
        while (i < num) {
            r = instantiate_free_var_mmv(abst_body(r), 0, arg(e, i));
            i = i + 1;
            if (!is_lambda(r))
                break;
        }
        if (i < num) {
            buffer<expr> args;
            args.push_back(r);
            for (; i < num; i++)
                args.push_back(arg(e, i));
            r = mk_app(args.size(), args.data());
        }
        return r;
    } else if (is_app(e) && is_constant(arg(e, 0))) {
        expr def = get_def_value(const_name(arg(e, 0)), env, defs);
        if (def)
            return update_app(e, 0, def);
    } else if (is_let(e)) {
        return instantiate_free_var_mmv(let_body(e), 0, let_value(e));
    } else if (is_constant(e)) {
        expr def = get_def_value(const_name(e), env, defs);
        if (def)
            return def;
    }
    return e;
}

}
