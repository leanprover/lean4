/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/metavar.h"
#include "kernel/free_vars.h"
#include "kernel/replace_visitor.h"
#include "kernel/justification.h"
#include "kernel/instantiate.h"

namespace lean {
bool substitution::is_assigned(name const & m) const {
    return m_subst.contains(m);
}

optional<std::pair<expr, justification>> substitution::get_assignment(name const & m) const {
    auto it = m_subst.find(m);
    if (it)
        return optional<std::pair<expr, justification>>(*it);
    else
        return optional<std::pair<expr, justification>>();
}

optional<expr> substitution::get_expr(name const & m) const {
    auto it = m_subst.find(m);
    if (it)
        return some_expr(it->first);
    else
        return none_expr();
}

void substitution::assign(name const & m, expr const & t, justification const & j) {
    lean_assert(closed(t));
    m_subst.insert(m, mk_pair(t, j));
}

void substitution::assign(name const & m, expr const & t) {
    assign(m, t, justification());
}

void substitution::for_each(std::function<void(name const & n, expr const & e, justification const & j)> const & fn) {
    m_subst.for_each([=](name const & n, std::pair<expr, justification> const & a) {
            fn(n, a.first, a.second);
        });
}

class instantiate_metavars_fn : public replace_visitor {
protected:
    substitution & m_subst;
    justification  m_jst;
    bool           m_use_jst;
    bool           m_update;

    void save_jst(justification const & j) { m_jst = mk_composite1(m_jst, j); }

    virtual expr visit_meta(expr const & m, context const &) {
        name const & m_name = mlocal_name(m);
        auto p1 = m_subst.get_assignment(m_name);
        if (p1) {
            if (!has_metavar(p1->first)) {
                if (m_use_jst)
                    save_jst(p1->second);
                return p1->first;
            } else if (m_use_jst) {
                if (m_update) {
                    auto p2 = d_instantiate_metavars(p1->first, m_subst);
                    justification new_jst = mk_composite1(p1->second, p2.second);
                    m_subst.assign(m_name, p2.first, new_jst);
                    save_jst(new_jst);
                    return p2.first;
                } else {
                    auto p2 = instantiate_metavars(p1->first, m_subst);
                    save_jst(mk_composite1(p1->second, p2.second));
                    return p2.first;
                }
            } else {
                if (m_update) {
                    expr r = d_instantiate_metavars_wo_jst(p1->first, m_subst);
                    m_subst.assign(m_name, r);
                    return r;
                } else {
                    return instantiate_metavars_wo_jst(p1->first, m_subst);
                }
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e, context const & ctx) {
        buffer<expr> args;
        expr const * it = &e;
        while (is_app(*it)) {
            args.push_back(visit(app_arg(*it), ctx));
            it = &app_fn(*it);
        }
        expr const & f = *it;
        if (is_metavar(f) && m_subst.is_assigned(mlocal_name(f))) {
            expr new_f = visit_meta(f, ctx);
            return apply_beta(new_f, args.size(), args.data());
        } else {
            args.push_back(visit(f, ctx));
            return update_rev_app(e, args);
        }
    }

public:
    instantiate_metavars_fn(substitution & s, bool use_jst, bool updt):
        m_subst(s), m_use_jst(use_jst), m_update(updt) {}
    justification const & get_justification() const { return m_jst; }
};

std::pair<expr, justification> instantiate_metavars(expr const & e, substitution const & s) {
    instantiate_metavars_fn fn(const_cast<substitution&>(s), true, false);
    expr r = fn(e);
    return mk_pair(r, fn.get_justification());
}

std::pair<expr, justification> d_instantiate_metavars(expr const & e, substitution & s) {
    instantiate_metavars_fn fn(s, true, true);
    expr r = fn(e);
    return mk_pair(r, fn.get_justification());
}

expr instantiate_metavars_wo_jst(expr const & e, substitution const & s) {
    return instantiate_metavars_fn(const_cast<substitution&>(s), false, false)(e);
}

expr d_instantiate_metavars_wo_jst(expr const & e, substitution & s) {
    return instantiate_metavars_fn(s, false, true)(e);
}
}
