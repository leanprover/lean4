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

    virtual format pp_header(formatter const & fmt, options const & opts, optional<metavar_env> const & menv) const {
        unsigned indent = get_pp_indent(opts);
        format expr_fmt = fmt(instantiate_metavars(menv, m_ctx), instantiate_metavars(menv, m_expr), false, opts);
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

void metavar_env_cell::inc_timestamp() {
    if (m_timestamp == std::numeric_limits<unsigned>::max()) {
        // This should not happen in real examples. We add it just to be safe.
        throw exception("metavar_env_cell timestamp overflow");
    }
    m_timestamp++;
}

metavar_env_cell::metavar_env_cell(name const & prefix):
    m_name_generator(prefix),
    m_beta_reduce_mv(true),
    m_timestamp(1),
    m_rc(0) {
}

static name g_default_name("M");
metavar_env_cell::metavar_env_cell():
    metavar_env_cell(g_default_name) {
}

metavar_env_cell::metavar_env_cell(metavar_env_cell const & other):
    m_name_generator(other.m_name_generator),
    m_metavar_data(other.m_metavar_data),
    m_beta_reduce_mv(other.m_beta_reduce_mv),
    m_timestamp(0),
    m_rc(0) {
}

expr metavar_env_cell::mk_metavar(context const & ctx, optional<expr> const & type) {
    inc_timestamp();
    name m = m_name_generator.next();
    expr r = ::lean::mk_metavar(m);
    m_metavar_data.insert(m, data(type, ctx));
    return r;
}

context metavar_env_cell::get_context(expr const & m) const {
    lean_assert(is_metavar(m));
    lean_assert(!has_local_context(m));
    return get_context(metavar_name(m));
}

context metavar_env_cell::get_context(name const & m) const {
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    return it->m_context;
}

expr metavar_env_cell::get_type(expr const & m) {
    lean_assert(is_metavar(m));
    expr t = get_type(metavar_name(m));
    if (has_local_context(m)) {
        if (is_metavar(t)) {
            return update_metavar(t, append(metavar_lctx(m), metavar_lctx(t)));
        } else {
            return apply_local_context(t, metavar_lctx(m), metavar_env(this));
        }
    } else {
        return t;
    }
}

expr metavar_env_cell::get_type(name const & m) {
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

bool metavar_env_cell::has_type(name const & m) const {
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    return static_cast<bool>(it->m_type);
}

bool metavar_env_cell::has_type(expr const & m) const {
    lean_assert(is_metavar(m));
    return has_type(metavar_name(m));
}

optional<justification> metavar_env_cell::get_justification(expr const & m) const {
    lean_assert(is_metavar(m));
    return get_justification(metavar_name(m));
}

optional<justification> metavar_env_cell::get_justification(name const & m) const {
    auto r = get_subst_jst(m);
    if (r)
        return optional<justification>(r->second);
    else
        return optional<justification>();
}

bool metavar_env_cell::is_assigned(name const & m) const {
    auto it = m_metavar_data.find(m);
    return it && it->m_subst;
}

bool metavar_env_cell::is_assigned(expr const & m) const {
    lean_assert(is_metavar(m));
    return is_assigned(metavar_name(m));
}

bool metavar_env_cell::assign(name const & m, expr const & t, justification const & jst) {
    lean_assert(!is_assigned(m));
    inc_timestamp();
    justification jst2 = jst;
    buffer<justification> jsts;
    expr t2 = instantiate_metavars(t, jsts);
    if (!jsts.empty()) {
        jst2 = justification(new normalize_assignment_justification(get_context(m), t, jst,
                                                                    jsts.size(), jsts.data()));
    }
    unsigned ctx_size = get_context_size(m);
    if (has_metavar(t2)) {
        bool failed = false;
        // Make sure the contexts of the metavariables occurring in \c t2 are
        // not too big.
        for_each(t2, [&](expr const & e, unsigned offset) {
                if (is_metavar(e)) {
                    lean_assert(!is_assigned(e));
                    unsigned range = free_var_range(e, metavar_env(this));
                    if (range > ctx_size + offset) {
                        unsigned extra = range - ctx_size - offset;
                        auto it2 = m_metavar_data.find(metavar_name(e));
                        if (it2 == nullptr) {
                            failed = true;
                        } else {
                            unsigned e_ctx_size = it2->m_context.size();
                            if (e_ctx_size < extra) {
                                failed = true;
                            } else {
                                it2->m_context = it2->m_context.truncate(e_ctx_size - extra);
                                lean_assert_le(free_var_range(e, metavar_env(this)), ctx_size + offset);
                            }
                        }
                    }
                }
                return true;
            });
        if (failed)
            return false;
    }
    if (free_var_range(t2, metavar_env(this)) > ctx_size)
        return false;
    auto it = m_metavar_data.find(m);
    lean_assert(it);
    it->m_subst         = t2;
    it->m_justification = jst2;
    return true;
}

bool metavar_env_cell::assign(name const & m, expr const & t) {
    justification j;
    return assign(m, t, j);
}

bool metavar_env_cell::assign(expr const & m, expr const & t, justification const & j) {
    lean_assert(is_metavar(m));
    lean_assert(!has_local_context(m));
    return assign(metavar_name(m), t, j);
}

bool metavar_env_cell::assign(expr const & m, expr const & t) {
    justification j;
    return assign(m, t, j);
}

expr apply_local_context(expr const & a, local_context const & lctx, optional<ro_metavar_env> const & menv) {
    if (lctx) {
        if (is_metavar(a)) {
            return mk_metavar(metavar_name(a), append(lctx, metavar_lctx(a)));
        } else {
            expr r = apply_local_context(a, tail(lctx), menv);
            local_entry const & e = head(lctx);
            if (e.is_lift()) {
                return lift_free_vars(r, e.s(), e.n(), menv);
            } else {
                lean_assert(e.is_inst());
                return instantiate(r, e.s(), e.v(), menv);
            }
        }
    } else {
        return a;
    }
}

optional<std::pair<expr, justification>> metavar_env_cell::get_subst_jst(expr const & m) const {
    lean_assert(is_metavar(m));
    auto p = get_subst_jst(metavar_name(m));
    if (p) {
        expr r = p->first;
        local_context const & lctx = metavar_lctx(m);
        if (lctx)
            r = apply_local_context(r, lctx, metavar_env(const_cast<metavar_env_cell*>(this)));
        return some(mk_pair(r, p->second));
    } else {
        return p;
    }
}

optional<std::pair<expr, justification>> metavar_env_cell::get_subst_jst(name const & m) const {
    auto it = const_cast<metavar_env_cell*>(this)->m_metavar_data.find(m);
    if (it->m_subst) {
        expr s = *(it->m_subst);
        if (has_assigned_metavar(s)) {
            buffer<justification> jsts;
            expr new_subst = instantiate_metavars(s, jsts);
            if (!jsts.empty()) {
                justification new_jst(new normalize_assignment_justification(it->m_context, s, it->m_justification,
                                                                             jsts.size(), jsts.data()));
                it->m_justification = new_jst;
                it->m_subst         = new_subst;
            }
        }
        return optional<std::pair<expr, justification>>(std::pair<expr, justification>(*(it->m_subst), it->m_justification));
    } else {
        return optional<std::pair<expr, justification>>();
    }
}

optional<expr> metavar_env_cell::get_subst(name const & m) const {
    auto r = get_subst_jst(m);
    if (r)
        return some_expr(r->first);
    else
        return none_expr();
}

optional<expr> metavar_env_cell::get_subst(expr const & m) const {
    auto r = get_subst_jst(m);
    if (r)
        return some_expr(r->first);
    else
        return none_expr();
}

bool metavar_env_cell::has_assigned_metavar(expr const & e) const {
    if (!has_metavar(e)) {
        return false;
    } else {
        bool result = false;
        for_each(e, [&](expr const & n, unsigned) {
                if (result)
                    return false;
                if (!has_metavar(n))
                    return false;
                if (is_metavar(n)) {
                    if (is_assigned(n)) {
                        result = true;
                        return false;
                    }
                    for (auto const & entry : metavar_lctx(n)) {
                        if (entry.is_inst() && has_assigned_metavar(entry.v())) {
                            result = true;
                            return false;
                        }
                    }
                }
                return true;
            });
        return result;
    }
}

bool metavar_env_cell::has_metavar(expr const & e, expr const & m) const {
    if (has_metavar(e)) {
        lean_assert(is_metavar(m));
        lean_assert(!is_assigned(m));
        return static_cast<bool>(find(e, [&](expr const & m2) {
                    return
                        is_metavar(m2) &&
                        ((metavar_name(m) == metavar_name(m2)) ||
                         (is_assigned(m2) && has_metavar(*get_subst(m2), m)));
                }));
    } else {
        return false;
    }
}

class instantiate_metavars_proc : public replace_visitor {
protected:
    metavar_env_cell const *  m_menv;
    buffer<justification> &   m_jsts;

    void push_back(justification const & jst) {
        if (jst)
            m_jsts.push_back(jst);
    }

    virtual expr visit_metavar(expr const & m, context const & ctx) {
        local_context const & lctx = metavar_lctx(m);
        if (is_metavar(m) && m_menv->is_assigned(m)) {
            auto p = m_menv->get_subst_jst(m);
            lean_assert(p);
            expr r = p->first;
            push_back(p->second);
            if (m_menv->has_assigned_metavar(r)) {
                return visit(r, ctx);
            } else {
                return r;
            }
        } else if (std::find_if(lctx.begin(), lctx.end(), [&](local_entry const & e) { return e.is_inst() && m_menv->has_assigned_metavar(e.v()); })
                   != lctx.end()) {
            // local context has assigned metavariables
            buffer<local_entry> new_lctx;
            for (auto const & e : lctx) {
                if (e.is_inst())
                    new_lctx.push_back(mk_inst(e.s(), visit(e.v(), ctx)));
                else
                    new_lctx.push_back(e);
            }
            return mk_metavar(metavar_name(m), to_list(new_lctx.begin(), new_lctx.end()));
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e, context const & ctx) {
        expr const & f = arg(e, 0);
        if (m_menv->beta_reduce_metavar_application() && is_metavar(f) && m_menv->is_assigned(f)) {
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
    instantiate_metavars_proc(metavar_env_cell const * menv, buffer<justification> & jsts):
        m_menv(menv),
        m_jsts(jsts) {
    }
};

expr metavar_env_cell::instantiate_metavars(expr const & e, buffer<justification> & jsts) const {
    if (!has_metavar(e)) {
        return e;
    } else {
        expr r = instantiate_metavars_proc(this, jsts)(e);
        lean_assert(!has_assigned_metavar(r));
        return r;
    }
}

context metavar_env_cell::instantiate_metavars(context const & ctx) const {
    buffer<context_entry> new_entries;
    auto it  = ctx.begin();
    auto end = ctx.end();
    for (; it != end; ++it) {
        auto n = it->get_name();
        auto d = it->get_domain();
        auto b = it->get_body();
        if (d && b)
            new_entries.emplace_back(n, instantiate_metavars(*d), instantiate_metavars(*b));
        else if (d)
            new_entries.emplace_back(n, instantiate_metavars(*d));
        else
            new_entries.emplace_back(n, none_expr(), instantiate_metavars(*b));
    }
    return context(new_entries.size(), new_entries.data());
}

metavar_env::metavar_env(ro_metavar_env const & s):m_ptr(s.m_ptr) {
    if (m_ptr) m_ptr->inc_ref();
}

template<typename MEnv>
bool cached_metavar_env_tpl<MEnv>::update(optional<MEnv> const & menv) {
    if (!menv) {
        m_menv = optional<MEnv>();
        if (m_timestamp != 0) {
            m_timestamp = 0;
            return true;
        } else {
            return false;
        }
    } else {
        unsigned new_timestamp = (*menv)->get_timestamp();
        if (m_menv != menv || m_timestamp != new_timestamp) {
            m_menv      = menv;
            m_timestamp = new_timestamp;
            return true;
        } else {
            return false;
        }
    }
}
template class cached_metavar_env_tpl<metavar_env>;
template class cached_metavar_env_tpl<ro_metavar_env>;

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

expr add_lift(expr const & m, unsigned s, unsigned n, optional<ro_metavar_env> const & menv) {
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

expr add_inst(expr const & m, unsigned s, expr const & v, optional<ro_metavar_env> const & menv) {
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
}
