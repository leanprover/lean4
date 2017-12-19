/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/replace_visitor.h"
#include "library/delayed_abstraction.h"

namespace lean {
/*
Helper functions for metavariable assignments.
The template parameter CTX must be an object that
provides the following API:

bool is_mvar(level const & l) const;
bool is_assigned(level const & l) const;
optional<level> get_assignment(level const & l) const;
void assign(level const & u, level const & v);

bool is_mvar(expr const & e) const;
bool is_assigned(expr const & e) const;
optional<expr> get_assignment(expr const & e) const;
void assign(expr const & m, expr const & v);

push_delayed_abstraction

bool in_tmp_mode() const;
*/

template<typename CTX>
bool has_assigned(CTX const & ctx, level const & l) {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (ctx.is_mvar(l) && ctx.is_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

template<typename CTX>
bool has_assigned(CTX const & ctx, levels const & ls) {
    for (level const & l : ls) {
        if (has_assigned(ctx, l))
            return true;
    }
    return false;
}

template<typename CTX>
bool has_assigned(CTX const & ctx, expr const & e) {
    if (!has_expr_metavar(e) && !has_univ_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((ctx.is_mvar(e) && ctx.is_assigned(e)) ||
                (is_constant(e) && has_assigned(ctx, const_levels(e))) ||
                (is_sort(e) && has_assigned(ctx, sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            if (is_metavar(e))
                return false; // do not search type
            return true; // continue search
        });
    return found;
}

template<typename CTX>
level instantiate_mvars(CTX & ctx, level const & l) {
    if (!has_assigned(ctx, l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (ctx.is_mvar(l)) {
                if (auto v1 = ctx.get_assignment(l)) {
                    level v2 = instantiate_mvars(ctx, *v1);
                    if (*v1 != v2) {
                        if (!ctx.in_tmp_mode())
                            ctx.assign(l, v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

template<typename CTX>
class instantiate_mvars_fn : public replace_visitor {
    CTX & m_ctx;
    bool  m_postpone_push_delayed;
    bool  m_found_delayed_abstraction{false};


    level visit_level(level const & l) {
        return instantiate_mvars(m_ctx, l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) override {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) override {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) override {
        return update_mlocal(e, visit(mlocal_type(e)));
    }

    virtual expr visit_meta(expr const & m) override {
        if (m_ctx.is_mvar(m)) {
            if (auto v1 = m_ctx.get_assignment(m)) {
                if (!has_metavar(*v1)) {
                    return *v1;
                } else {
                    expr v2 = visit(*v1);
                    if (!m_ctx.in_tmp_mode() && v2 != *v1)
                        m_ctx.assign(m, v2);
                    return v2;
                }
            } else {
                return m;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (m_ctx.is_mvar(f)) {
            if (auto v = m_ctx.get_assignment(f)) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_metavar(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) override {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        expr r = update_macro(e, new_args.size(), new_args.data());
        if (is_delayed_abstraction(r)) {
            if (m_postpone_push_delayed) {
                m_found_delayed_abstraction = true;
            } else {
                return push_delayed_abstraction(r);
            }
        }
        return r;
    }

    virtual expr visit(expr const & e) override {
        if (!has_expr_metavar(e) && !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_mvars_fn(CTX & ctx, bool postpone_push_delayed):m_ctx(ctx), m_postpone_push_delayed(postpone_push_delayed) {}
    expr operator()(expr const & e) {
        expr r = visit(e);
        if (m_found_delayed_abstraction) {
            buffer<name> ns; buffer<expr> es;
            r = append_delayed_abstraction(r, ns, es);
        }
        return r;
    }
};

template<typename CTX>
expr instantiate_mvars(CTX & ctx, expr const & e, bool postpone_push_delayed) {
    if (!has_assigned(ctx, e))
        return e;
    expr r = instantiate_mvars_fn<CTX>(ctx, postpone_push_delayed)(e);
    lean_assert(!has_assigned(ctx, r));
    return r;
}
}
