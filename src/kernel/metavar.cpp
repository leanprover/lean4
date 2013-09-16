/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/exception.h"
#include "kernel/metavar.h"
#include "kernel/replace.h"
#include "kernel/free_vars.h"
#include "kernel/occurs.h"
#include "kernel/for_each.h"

namespace lean {
void metavar_env::inc_timestamp() {
    if (m_timestamp == std::numeric_limits<unsigned>::max()) {
        // This should not happen in real examples. We add it just to be safe.
        throw exception("metavar_env timestamp overflow");
    }
    m_timestamp++;
}

metavar_env::metavar_env():m_timestamp(0) {}

expr metavar_env::mk_metavar(context const & ctx) {
    inc_timestamp();
    unsigned midx = m_env.size();
    m_env.push_back(data(ctx));
    return ::lean::mk_metavar(midx);
}

bool metavar_env::contains(unsigned midx) const {
    return midx < m_env.size();
}

bool metavar_env::is_assigned(unsigned midx) const {
    return m_env[midx].m_subst;
}

expr metavar_env::get_subst(unsigned midx) const {
    return m_env[midx].m_subst;
}

expr metavar_env::get_type(unsigned midx, unification_problems & up) {
    auto p = m_env[midx];
    expr t = p->m_type;
    if (t) {
        return t;
    } else {
        t = mk_metavar();
        expr s = p->m_subst;
        m_env[midx] = data(s, t, p->m_ctx);
        if (s)
            up.add_type_of_eq(p->m_ctx, s, t);
        else
            up.add_type_of_eq(p->m_ctx, ::lean::mk_metavar(midx), t);
        return t;
    }
}

void metavar_env::assign(unsigned midx, expr const & v) {
    inc_timestamp();
    lean_assert(!is_assigned(midx));
    auto p = m_env[midx];
    m_env[midx] = data(v, p->m_type, p->m_ctx);
}

expr subst(expr const & a, unsigned i, expr const & c) {
    auto f = [&](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx == offset + i)
                return lift_free_vars(c, 0, offset);
            else
                return e;
        } else if (is_metavar(e)) {
            return add_subst(e, offset, lift_free_vars(c, 0, offset));
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}

expr instantiate(expr const & s, meta_ctx const & ctx, metavar_env const & env) {
    if (ctx) {
        expr r = instantiate(s, tail(ctx), env);
        meta_entry const & e = head(ctx);
        switch (e.kind()) {
        case meta_entry_kind::Lift:   return lift_free_vars(r, e.s(), e.n());
        case meta_entry_kind::Lower:  return lower_free_vars(r, e.s(), e.n());
        case meta_entry_kind::Subst:  return subst(r, e.s(), instantiate_metavars(e.v(), env));
        }
        lean_unreachable();
        return s;
    } else {
        return s;
    }
}

expr metavar_env::get_subst(expr const & m) const {
    expr s = get_subst(metavar_idx(m));
    if (s)
        return instantiate(s, metavar_ctx(m), *this);
    else
        return s;
}

expr metavar_env::get_type(expr const & m, unification_problems & up) {
    expr s = get_type(metavar_idx(m), up);
    lean_assert(is_metavar(s));
    lean_assert(!metavar_ctx(s));
    meta_ctx const & ctx = metavar_ctx(m);
    if (ctx)
        return ::lean::mk_metavar(metavar_idx(s), ctx);
    else
        return s;
}

void metavar_env::assign(expr const & m, expr const & t) {
    lean_assert(!metavar_ctx(m));
    assign(metavar_idx(m), t);
}

expr instantiate_metavars(expr const & e, metavar_env const & env) {
    auto f = [=](expr const & m, unsigned offset) -> expr {
        if (is_metavar(m) && env.contains(m)) {
            expr s = env.get_subst(m);
            return s ? s : m;
        } else {
            return m;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}

expr add_lift(expr const & m, unsigned s, unsigned n) {
    return mk_metavar(metavar_idx(m), cons(mk_lift(s, n), metavar_ctx(m)));
}

meta_ctx add_lower(meta_ctx const & ctx, unsigned s2, unsigned n2) {
    if (ctx) {
        meta_entry e = head(ctx);
        unsigned s1, n1;
        switch (e.kind()) {
        case meta_entry_kind::Lift:
            s1 = e.s();
            n1 = e.n();
            if (s1 <= s2 && s2 <= s1 + n1) {
                if (n1 == n2)
                    return tail(ctx);
                else if (n1 > n2)
                    return cons(mk_lift(s1, n1 - n2), tail(ctx));
            }
            break;
        case meta_entry_kind::Lower:
            s1 = e.s();
            n1 = e.n();
            if (s2 == s1 - n1)
                return add_lower(tail(ctx), s1, n1 + n2);
            break;
        case meta_entry_kind::Subst:
            break;
        }
    }
    return cons(mk_lower(s2, n2), ctx);
}

expr add_lower(expr const & m, unsigned s, unsigned n) {
    return mk_metavar(metavar_idx(m), add_lower(metavar_ctx(m), s, n));
}

meta_ctx add_subst(meta_ctx const & ctx, unsigned s, expr const & v) {
    if (ctx) {
        meta_entry e = head(ctx);
        switch (e.kind()) {
        case meta_entry_kind::Subst:
            return cons(mk_subst(s, v), ctx);
        case meta_entry_kind::Lower:
            if (s >= e.s())
                return cons(e, add_subst(tail(ctx), s + e.n(), lift_free_vars(v, e.s(), e.n())));
            else
                return cons(e, add_subst(tail(ctx), s, lift_free_vars(v, e.s(), e.n())));
        case meta_entry_kind::Lift:
            if (e.s() <= s && s < e.s() + e.n()) {
                return ctx;
            } else if (s < e.s() && !has_free_var(v, e.s(), std::numeric_limits<unsigned>::max())) {
                return cons(e, add_subst(tail(ctx), s, v));
            } else if (s >= e.s() + e.n() && !has_free_var(v, e.s(), std::numeric_limits<unsigned>::max())) {
                return cons(e, add_subst(tail(ctx), s - e.n(), v));
            } else {
                return cons(mk_subst(s, v), ctx);
            }
        }
        lean_unreachable();
        return ctx;
    } else {
        return cons(mk_subst(s, v), ctx);
    }
}

expr add_subst(expr const & m, unsigned s, expr const & v) {
    return mk_metavar(metavar_idx(m), add_subst(metavar_ctx(m), s, v));
}

bool has_context(expr const & m) {
    return metavar_ctx(m);
}

expr pop_context(expr const & m) {
    lean_assert(has_context(m));
    return mk_metavar(metavar_idx(m), tail(metavar_ctx(m)));
}

/**
   \brief Auxiliary exception used to sign that a metavariable was
   found in an expression.
*/
struct found_metavar {};

bool has_metavar(expr const & e, unsigned midx, metavar_env const & menv) {
    auto f = [&](expr const & m, unsigned offset) {
        if (is_metavar(m)) {
            unsigned midx2 = metavar_idx(m);
            if (midx2 == midx)
                throw found_metavar();
            if (menv.contains(midx2) &&
                menv.is_assigned(midx2) &&
                has_metavar(menv.get_subst(midx2), midx, menv))
                throw found_metavar();
        }
    };
    try {
        for_each_fn<decltype(f)> proc(f);
        proc(e);
        return false;
    } catch (found_metavar) {
        return true;
    }
}
}
