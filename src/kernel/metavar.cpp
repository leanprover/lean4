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
#include "kernel/instantiate.h"
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

expr metavar_env::mk_metavar(expr const & type, context const & ctx) {
    inc_timestamp();
    unsigned midx = m_env.size();
    m_env.push_back(data(type, ctx));
    return ::lean::mk_metavar(midx);
}

expr metavar_env::mk_metavar(context const & ctx) {
    return mk_metavar(expr(), ctx);
}

bool metavar_env::contains(unsigned midx) const {
    return midx < m_env.size();
}

bool metavar_env::is_assigned(unsigned midx) const {
    return m_env[midx].m_subst;
}

expr metavar_env::get_subst_core(unsigned midx) const {
    return m_env[midx].m_subst;
}

expr metavar_env::get_subst(unsigned midx) const {
    expr r = m_env[midx].m_subst;
    if (r && has_assigned_metavar(r, *this)) {
        r = instantiate_metavars(r, *this);
        expr t      = m_env[midx].m_type;
        context ctx = m_env[midx].m_ctx;
        const_cast<metavar_env*>(this)->m_env[midx] = data(r, t, ctx);
        return r;
    } else {
        return r;
    }
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

expr metavar_env::get_type(unsigned midx) const {
    return m_env[midx].m_type;
}

void metavar_env::assign(unsigned midx, expr const & v) {
    inc_timestamp();
    lean_assert(!is_assigned(midx));
    auto p = m_env[midx];
    m_env[midx] = data(v, p->m_type, p->m_ctx);
}

context const & metavar_env::get_context(unsigned midx) const {
    return m_env[midx].m_ctx;
}

expr instantiate(expr const & s, meta_ctx const & ctx, metavar_env const & env) {
    if (ctx) {
        expr r = instantiate(s, tail(ctx), env);
        meta_entry const & e = head(ctx);
        if (e.is_lift()) {
            return lift_free_vars(r, e.s(), e.n());
        } else {
            lean_assert(e.is_inst());
            return ::lean::instantiate(r, e.s(), instantiate_metavars(e.v(), env));
        }
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
    return instantiate(s, metavar_ctx(m), *this);
}

void metavar_env::assign(expr const & m, expr const & t) {
    lean_assert(!metavar_ctx(m));
    assign(metavar_idx(m), t);
}

expr instantiate_metavars(expr const & e, metavar_env const & env) {
    if (!has_metavar(e)) {
        return e;
    } else {
        auto f = [=](expr const & m, unsigned) -> expr {
            if (is_metavar(m) && env.contains(m)) {
                expr s = env.get_subst(m);
                return s ? s : m;
            } else {
                return m;
            }
        };
        return replace_fn<decltype(f)>(f)(e);
    }
}

meta_ctx add_lift(meta_ctx const & ctx, unsigned s, unsigned n) {
    if (n == 0) {
        return ctx;
    } else if (ctx) {
        meta_entry e = head(ctx);
        // Simplification rule
        //    lift:(s1+n1):n2 lift:s1:n1 --->  lift:s1:n1+n2
        if (e.is_lift() && s == e.s() + e.n()) {
            return add_lift(tail(ctx), e.s(), e.n() + n);
        }
    }
    return cons(mk_lift(s, n), ctx);
}

expr add_lift(expr const & m, unsigned s, unsigned n) {
    return mk_metavar(metavar_idx(m), add_lift(metavar_ctx(m), s, n));
}

meta_ctx add_inst(meta_ctx const & ctx, unsigned s, expr const & v) {
    if (ctx) {
        meta_entry e = head(ctx);
        if (e.is_lift() && e.s() <= s && s < e.s() + e.n()) {
            return add_lift(tail(ctx), e.s(), e.n() - 1);
        }
        // Simplifications such as
        //   inst:4 #6  lift:5:3  -->  lift:4:2
        //   inst:3 #7  lift:4:5 -->   lift:3:4
        // General rule is:
        //   inst:(s-1) #(s+n-2)  lift:s:n  --> lift:s-1:n-1
        if (e.is_lift() && is_var(v) && e.s() > 0 && s == e.s() - 1 && e.s() + e.n() > 2 && var_idx(v) == e.s() + e.n() - 2) {
            return add_lift(tail(ctx), e.s() - 1, e.n() - 1);
        }
    }
    return cons(mk_inst(s, v), ctx);
}

expr add_inst(expr const & m, unsigned s, expr const & v) {
    return mk_metavar(metavar_idx(m), add_inst(metavar_ctx(m), s, v));
}

bool has_meta_context(expr const & m) {
    return metavar_ctx(m);
}

expr pop_meta_context(expr const & m) {
    lean_assert(has_meta_context(m));
    return mk_metavar(metavar_idx(m), tail(metavar_ctx(m)));
}

struct found_assigned {};
bool has_assigned_metavar(expr const & e, metavar_env const & menv) {
    if (!has_metavar(e)) {
        return false;
    } else {
        auto proc = [&](expr const & n, unsigned) {
            if (is_metavar(n) && menv.contains(n) && menv.is_assigned(n))
                throw found_assigned();
        };
        for_each_fn<decltype(proc)> visitor(proc);
        try {
            visitor(e);
            return false;
        } catch (found_assigned&) {
            return true;
        }
    }
}

/**
   \brief Auxiliary exception used to sign that a metavariable was
   found in an expression.
*/
struct found_metavar {};

bool has_metavar(expr const & e, unsigned midx, metavar_env const & menv) {
    auto f = [&](expr const & m, unsigned) {
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
