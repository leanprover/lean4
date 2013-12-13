/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <limits>
#include <algorithm>
#include "util/exception.h"
#include "kernel/metavar.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/occurs.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"

namespace lean {
/**
   \brief Assignment normalization justification. That is, when other assignments are applied to an existing assignment.
*/
class normalize_assignment_justification : public justification_cell {
    context                    m_ctx;
    expr                       m_expr;
    std::vector<justification> m_jsts;
public:
    normalize_assignment_justification(context const & ctx, expr const & e,
                                       justification const & jst,
                                       unsigned num_assignment_jsts, justification const * assignment_jsts):
        m_ctx(ctx),
        m_expr(e),
        m_jsts(assignment_jsts, assignment_jsts + num_assignment_jsts) {
        m_jsts.push_back(jst);
        std::reverse(m_jsts.begin(), m_jsts.end());
    }

    virtual format pp_header(formatter const & fmt, options const & opts) const {
        unsigned indent = get_pp_indent(opts);
        format expr_fmt = fmt(m_ctx, m_expr, false, opts);
        format r;
        r += format("Normalize assignment");
        r += nest(indent, compose(line(), expr_fmt));
        return r;
    }

    virtual void get_children(buffer<justification_cell*> & r) const {
        append(r, m_jsts);
    }

    virtual optional<expr> get_main_expr() const { return some_expr(m_expr); }
};

void swap(metavar_env & a, metavar_env & b) {
    swap(a.m_name_generator,         b.m_name_generator);
    swap(a.m_metavar_data,           b.m_metavar_data);
    std::swap(a.m_beta_reduce_mv,    b.m_beta_reduce_mv);
    std::swap(a.m_timestamp,         b.m_timestamp);
}

void metavar_env::inc_timestamp() {
    if (m_timestamp == std::numeric_limits<unsigned>::max()) {
        // This should not happen in real examples. We add it just to be safe.
        throw exception("metavar_env timestamp overflow");
    }
    m_timestamp++;
}

metavar_env::metavar_env(name const & prefix):
    m_name_generator(prefix),
    m_beta_reduce_mv(true),
    m_timestamp(0) {
}

static name g_default_name("M");
metavar_env::metavar_env():
    metavar_env(g_default_name) {
}

expr metavar_env::mk_metavar(context const & ctx, optional<expr> const & type) {
    inc_timestamp();
    name m = m_name_generator.next();
    expr r = ::lean::mk_metavar(m);
    m_metavar_data.insert(m, data(type, ctx));
    return r;
}

context metavar_env::get_context(expr const & m) const {
    lean_assert(is_metavar(m));
    lean_assert(!has_local_context(m));
    return get_context(metavar_name(m));
}

context metavar_env::get_context(name const & m) const {
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    return it->m_context;
}

expr metavar_env::get_type(expr const & m) {
    lean_assert(is_metavar(m));
    expr t = get_type(metavar_name(m));
    if (has_local_context(m)) {
        if (is_metavar(t)) {
            return update_metavar(t, append(metavar_lctx(m), metavar_lctx(t)));
        } else {
            return apply_local_context(t, metavar_lctx(m));
        }
    } else {
        return t;
    }
}

expr metavar_env::get_type(name const & m) {
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    if (it->m_type) {
        return *(it->m_type);
    } else {
        expr t = mk_metavar(get_context(m));
        it->m_type = t;
        return t;
    }
}

bool metavar_env::has_type(name const & m) const {
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    return static_cast<bool>(it->m_type);
}

bool metavar_env::has_type(expr const & m) const {
    lean_assert(is_metavar(m));
    return has_type(metavar_name(m));
}

optional<justification> metavar_env::get_justification(expr const & m) const {
    lean_assert(is_metavar(m));
    return get_justification(metavar_name(m));
}

optional<justification> metavar_env::get_justification(name const & m) const {
    auto r = get_subst_jst(m);
    if (r)
        return optional<justification>(r->second);
    else
        return optional<justification>();
}

bool metavar_env::is_assigned(name const & m) const {
    auto it = m_metavar_data.find(m);
    return it && it->m_subst;
}

bool metavar_env::is_assigned(expr const & m) const {
    lean_assert(is_metavar(m));
    return is_assigned(metavar_name(m));
}

void metavar_env::assign(name const & m, expr const & t, justification const & jst) {
    lean_assert(!is_assigned(m));
    inc_timestamp();
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    it->m_subst         = t;
    it->m_justification = jst;
}

void metavar_env::assign(expr const & m, expr const & t, justification const & j) {
    lean_assert(is_metavar(m));
    lean_assert(!has_local_context(m));
    assign(metavar_name(m), t, j);
}

expr apply_local_context(expr const & a, local_context const & lctx) {
    if (lctx) {
        if (is_metavar(a)) {
            return mk_metavar(metavar_name(a), append(lctx, metavar_lctx(a)));
        } else {
            expr r = apply_local_context(a, tail(lctx));
            local_entry const & e = head(lctx);
            if (e.is_lift()) {
                return lift_free_vars(r, e.s(), e.n());
            } else {
                lean_assert(e.is_inst());
                return instantiate(r, e.s(), e.v());
            }
        }
    } else {
        return a;
    }
}

optional<std::pair<expr, justification>> metavar_env::get_subst_jst(expr const & m) const {
    lean_assert(is_metavar(m));
    auto p = get_subst_jst(metavar_name(m));
    if (p) {
        expr r = p->first;
        local_context const & lctx = metavar_lctx(m);
        if (lctx)
            r = apply_local_context(r, lctx);
        return some(mk_pair(r, p->second));
    } else {
        return p;
    }
}

optional<std::pair<expr, justification>> metavar_env::get_subst_jst(name const & m) const {
    auto it = const_cast<metavar_env*>(this)->m_metavar_data.find(m);
    if (it->m_subst) {
        expr s = *(it->m_subst);
        if (has_assigned_metavar(s, *this)) {
            buffer<justification> jsts;
            expr new_subst = instantiate_metavars(s, *this, jsts);
            if (!jsts.empty()) {
                it->m_justification = justification(new normalize_assignment_justification(it->m_context, s, it->m_justification,
                                                                                           jsts.size(), jsts.data()));
                it->m_subst         = new_subst;
            }
        }
        return optional<std::pair<expr, justification>>(std::pair<expr, justification>(*(it->m_subst), it->m_justification));
    } else {
        return optional<std::pair<expr, justification>>();
    }
}

optional<expr> metavar_env::get_subst(name const & m) const {
    auto r = get_subst_jst(m);
    if (r)
        return some_expr(r->first);
    else
        return none_expr();
}

optional<expr> metavar_env::get_subst(expr const & m) const {
    auto r = get_subst_jst(m);
    if (r)
        return some_expr(r->first);
    else
        return none_expr();
}

class instantiate_metavars_proc : public replace_visitor {
protected:
    metavar_env const &     m_menv;
    buffer<justification> & m_jsts;

    void push_back(justification const & jst) {
        if (jst)
            m_jsts.push_back(jst);
    }

    virtual expr visit_metavar(expr const & m, context const & ctx) {
        if (is_metavar(m) && m_menv.is_assigned(m)) {
            auto p = m_menv.get_subst_jst(m);
            lean_assert(p);
            expr r = p->first;
            push_back(p->second);
            if (has_assigned_metavar(r, m_menv)) {
                return visit(r, ctx);
            } else {
                return r;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e, context const & ctx) {
        expr const & f = arg(e, 0);
        if (m_menv.beta_reduce_metavar_application() && is_metavar(f) && m_menv.is_assigned(f)) {
            buffer<expr> new_args;
            for (unsigned i = 0; i < num_args(e); i++)
                new_args.push_back(visit(arg(e, i), ctx));
            if (is_lambda(new_args[0]))
                return apply_beta(new_args[0], new_args.size() - 1, new_args.data() + 1);
            else
                return mk_app(new_args);
        } else {
            return replace_visitor::visit_app(e, ctx);
        }
    }

public:
    instantiate_metavars_proc(metavar_env const & menv, buffer<justification> & jsts):
        m_menv(menv),
        m_jsts(jsts) {
    }
};

expr instantiate_metavars(expr const & e, metavar_env const & menv, buffer<justification> & jsts) {
    if (!has_metavar(e)) {
        return e;
    } else {
        return instantiate_metavars_proc(menv, jsts)(e);
    }
}

bool has_assigned_metavar(expr const & e, metavar_env const & menv) {
    if (!has_metavar(e)) {
        return false;
    } else {
        bool result = false;
        for_each(e, [&](expr const & n, unsigned) {
                if (result)
                    return false;
                if (!has_metavar(n))
                    return false;
                if (is_metavar(n) && menv.is_assigned(n)) {
                    result = true;
                    return false;
                }
                return true;
            });
        return result;
    }
}

local_context add_lift(local_context const & lctx, unsigned s, unsigned n) {
    if (n == 0)
        return lctx;
    if (lctx) {
        local_entry e = head(lctx);
        // Simplification rule
        //    lift:s2:n2 lift:s1:n1 --->  lift:s1:n1+n2   when s1 <= s2 <= s1 + n1
        if (e.is_lift() && e.s() <= s && s <= e.s() + e.n()) {
            return add_lift(tail(lctx), e.s(), e.n() + n);
        }
    }
    return cons(mk_lift(s, n), lctx);
}

expr add_lift(expr const & m, unsigned s, unsigned n, metavar_env const * menv) {
    if (menv && s >= free_var_range(m, *menv))
        return m;
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

expr add_inst(expr const & m, unsigned s, expr const & v, metavar_env const * menv) {
    if (menv && s >= free_var_range(m, *menv))
        return m;
    return update_metavar(m, add_inst(metavar_lctx(m), s, v));
}

bool has_local_context(expr const & m) {
    return static_cast<bool>(metavar_lctx(m));
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

bool has_metavar(expr const & e, expr const & m, metavar_env const & menv) {
    if (has_metavar(e)) {
        lean_assert(is_metavar(m));
        lean_assert(!menv.is_assigned(m));
        return static_cast<bool>(find(e, [&](expr const & m2) {
                    return
                        is_metavar(m2) &&
                        ((metavar_name(m) == metavar_name(m2)) ||
                         (menv.is_assigned(m2) && has_metavar(*menv.get_subst(m2), m, menv)));
                }));
    } else {
        return false;
    }
}
}
