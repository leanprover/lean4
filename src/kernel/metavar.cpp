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
void substitution::inc_timestamp() {
    if (m_timestamp == std::numeric_limits<unsigned>::max()) {
        // This should not happen in real examples. We add it just to be safe.
        throw exception("metavar_env timestamp overflow");
    }
    m_timestamp++;
}

substitution::substitution():
    m_size(0),
    m_timestamp(0) {
}

bool substitution::operator==(substitution const & s) const {
    if (size() != s.size())
        return false;
    // TODO(Leo)
    return true;
}

bool substitution::is_assigned(name const & m) const {
    return const_cast<substitution*>(this)->m_subst.splay_find(m);
}

bool substitution::is_assigned(expr const & m) const {
    return is_assigned(metavar_name(m));
}

void substitution::assign(name const & m, expr const & t) {
    lean_assert(!is_assigned(m));
    m_subst.insert(m, t);
    inc_timestamp();
    m_size++;
}

void substitution::assign(expr const & m, expr const & t) {
    lean_assert(is_metavar(m));
    lean_assert(!has_local_context(m));
    assign(metavar_name(m), t);
}

expr apply_local_context(expr const & a, local_context const & lctx) {
    if (lctx) {
        expr r = apply_local_context(a, tail(lctx));
        local_entry const & e = head(lctx);
        if (e.is_lift()) {
            return lift_free_vars(r, e.s(), e.n());
        } else {
            lean_assert(e.is_inst());
            return instantiate(r, e.s(), e.v());
        }
    } else {
        return a;
    }
}

expr substitution::get_subst(expr const & m) const {
    lean_assert(is_metavar(m));
    name2expr::entry const * e = const_cast<substitution*>(this)->m_subst.splay_find(metavar_name(m));
    if (e) {
        expr r = e->second;
        if (has_assigned_metavar(r, *this)) {
            r = instantiate_metavars(r, *this);
            const_cast<substitution*>(this)->m_subst.insert(metavar_name(m), r);
        }
        local_context const & lctx = metavar_lctx(m);
        if (lctx) {
            r = apply_local_context(r, lctx);
            if (has_assigned_metavar(r, *this))
                r = instantiate_metavars(r, *this);
        }
        return r;
    } else {
        return expr();
    }
}

static name g_unique_name = name::mk_internal_unique_name();

metavar_generator::metavar_generator(name const & prefix):
    m_gen(prefix) {
}

metavar_generator::metavar_generator():
    m_gen(g_unique_name) {
}

expr metavar_generator::mk(expr const & t) {
    return mk_metavar(m_gen.next(), t, local_context());
}

expr metavar_generator::mk() {
    return mk(mk(expr()));
}

expr instantiate_metavars(expr const & e, substitution const & s) {
    if (!has_metavar(e)) {
        return e;
    } else {
        auto f = [=](expr const & m, unsigned) -> expr {
            if (is_metavar(m) && s.is_assigned(m)) {
                return s.get_subst(m);
            } else {
                return m;
            }
        };
        return replace_fn<decltype(f)>(f)(e);
    }
}

struct found_assigned {};
bool has_assigned_metavar(expr const & e, substitution const & s) {
    if (!has_metavar(e)) {
        return false;
    } else {
        auto proc = [&](expr const & n, unsigned) {
            if (is_metavar(n) && s.is_assigned(n))
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

local_context add_lift(local_context const & lctx, unsigned s, unsigned n) {
    if (n == 0) {
        return lctx;
    } else if (lctx) {
        local_entry e = head(lctx);
        // Simplification rule
        //    lift:(s1+n1):n2 lift:s1:n1 --->  lift:s1:n1+n2
        if (e.is_lift() && s == e.s() + e.n()) {
            return add_lift(tail(lctx), e.s(), e.n() + n);
        }
    }
    return cons(mk_lift(s, n), lctx);
}

expr add_lift(expr const & m, unsigned s, unsigned n) {
    return update_metavar(m, add_lift(metavar_lctx(m), s, n));
}

local_context add_inst(local_context const & lctx, unsigned s, expr const & v) {
    if (lctx) {
        local_entry e = head(lctx);
        if (e.is_lift() && e.s() <= s && s < e.s() + e.n()) {
            return add_lift(tail(lctx), e.s(), e.n() - 1);
        }
        // Simplifications such as
        //   inst:4 #6  lift:5:3  -->  lift:4:2
        //   inst:3 #7  lift:4:5 -->   lift:3:4
        // General rule is:
        //   inst:(s-1) #(s+n-2)  lift:s:n  --> lift:s-1:n-1
        if (e.is_lift() && is_var(v) && e.s() > 0 && s == e.s() - 1 && e.s() + e.n() > 2 && var_idx(v) == e.s() + e.n() - 2) {
            return add_lift(tail(lctx), e.s() - 1, e.n() - 1);
        }
    }
    return cons(mk_inst(s, v), lctx);
}

expr add_inst(expr const & m, unsigned s, expr const & v) {
    return update_metavar(m, add_inst(metavar_lctx(m), s, v));
}

bool has_local_context(expr const & m) {
    return metavar_lctx(m);
}

expr pop_meta_context(expr const & m) {
    lean_assert(has_local_context(m));
    return update_metavar(m, tail(metavar_lctx(m)));
}

/**
   \brief Auxiliary exception used to sign that a metavariable was
   found in an expression.
*/
struct found_metavar {};

bool has_metavar(expr const & e, expr const & m, substitution const & s) {
    lean_assert(is_metavar(m));
    lean_assert(!s.is_assigned(m));
    auto f = [&](expr const & m2, unsigned) {
        if (is_metavar(m2)) {
            if (metavar_name(m) == metavar_name(m2))
                throw found_metavar();
            if (s.is_assigned(m2) &&
                has_metavar(s.get_subst(m2), m, s))
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
