/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "metavar.h"
#include "replace.h"
#include "for_each.h"

namespace lean {
static name g_metavar_prefix(name(name(name(0u), "library"), "metavar"));
static name g_subst_prefix(name(name(name(0u), "library"), "subst"));
static name g_lift_prefix(name(name(name(0u), "library"), "lift"));
static name g_lower_prefix(name(name(name(0u), "library"), "lower"));

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
    return mk_app(mk_subst_fn(i), e, c);
}

bool is_subst(expr const & e, unsigned & i, expr & c) {
    if (is_app(e) && is_subst_fn(arg(e,0))) {
        i = const_name(arg(e,0)).get_numeral();
        c = arg(e,2);
        return true;
    } else {
        return false;
    }
}

bool is_subst(expr const & e) {
    return is_app(e) && is_subst_fn(arg(e,0));
}

expr mk_lift_fn(unsigned s, unsigned n) {
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
    return mk_app(mk_lift_fn(s, n), e);
}

bool is_lift(expr const & e, unsigned & s, unsigned & n) {
    if (is_app(e) && is_lift_fn(arg(e,0))) {
        name const & l = const_name(arg(e,0));
        n = l.get_numeral();
        s = l.get_prefix().get_numeral();
        return true;
    } else {
        return false;
    }
}

bool is_lift(expr const & e) {
    return is_app(e) && is_lift_fn(arg(e,0));
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

expr mk_lower(expr const & e, unsigned s, unsigned n) {
    return mk_app(mk_lower_fn(s, n), e);
}

bool is_lower(expr const & e, unsigned & s, unsigned & n) {
    if (is_app(e) && is_lower_fn(arg(e,0))) {
        name const & l = const_name(arg(e,0));
        n = l.get_numeral();
        s = l.get_prefix().get_numeral();
        return true;
    } else {
        return false;
    }
}

bool is_lower(expr const & e) {
    return is_app(e) && is_lower_fn(arg(e,0));
}

bool is_meta(expr const & e) {
    return is_metavar(e) || is_subst(e) || is_lift(e) || is_lower(e);
}

expr lower_free_vars_mmv(expr const & e, unsigned s, unsigned n) {
    if (n == 0)
        return e;
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
    return replace_fn<decltype(f)>(f)(e);
}

expr lift_free_vars_mmv(expr const & e, unsigned s, unsigned n) {
    if (n == 0)
        return e;
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= s + offset) {
            return mk_var(var_idx(e) + n);
        } else if (is_meta(e)) {
            return mk_lift(e, s + offset, n);
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}

expr instantiate_free_var_mmv(expr const & e, unsigned i, expr const & c) {
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
    return replace_fn<decltype(f)>(f)(e);
}

expr subst_mmv(expr const & e, unsigned i, expr const & c) {
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
    return replace_fn<decltype(f)>(f)(e);
}

expr get_metavar(expr const & e) {
    lean_assert(is_meta(e));
    if (is_metavar(e)) {
        return e;
    } else {
        return get_metavar(arg(e, 1));
    }
}

expr instantiate_metavar_core(expr const & e, expr const & v) {
    lean_assert(is_meta(e));
    unsigned i, s, n;
    expr c;
    if (is_metavar(e)) {
        return v;
    } else if (is_subst(e, i, c)) {
        return subst_mmv(instantiate_metavar_core(arg(e, 1), v), i, c);
    } else if (is_lift(e, s, n)) {
        return lift_free_vars_mmv(instantiate_metavar_core(arg(e, 1), v), s, n);
    } else if (is_lower(e, s, n)) {
        return lower_free_vars_mmv(instantiate_metavar_core(arg(e, 1), v), s, n);
    } else {
        lean_unreachable();
        return e;
    }
}

expr instantiate_metavar(expr const & e, unsigned midx, expr const & v) {
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
    return replace_fn<decltype(f)>(f)(e);
}
}
