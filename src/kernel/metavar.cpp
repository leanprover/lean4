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
#include "kernel/find_fn.h"
#include "kernel/level.h"

namespace lean {
bool substitution::is_expr_assigned(name const & m) const {
    return m_expr_subst.contains(m);
}

optional<std::pair<expr, justification>> substitution::get_expr_assignment(name const & m) const {
    auto it = m_expr_subst.find(m);
    if (it)
        return optional<std::pair<expr, justification>>(*it);
    else
        return optional<std::pair<expr, justification>>();
}

bool substitution::is_level_assigned(name const & m) const {
    return m_level_subst.contains(m);
}

optional<std::pair<level, justification>> substitution::get_level_assignment(name const & m) const {
    auto it = m_level_subst.find(m);
    if (it)
        return opt_level_jst(*it);
    else
        return opt_level_jst();
}

optional<expr> substitution::get_expr(name const & m) const {
    auto it = m_expr_subst.find(m);
    if (it)
        return some_expr(it->first);
    else
        return none_expr();
}

optional<level> substitution::get_level(name const & m) const {
    auto it = m_level_subst.find(m);
    if (it)
        return some_level(it->first);
    else
        return none_level();
}

void substitution::assign(name const & m, expr const & t, justification const & j) {
    lean_assert(closed(t));
    m_expr_subst.insert(m, mk_pair(t, j));
}

void substitution::assign(name const & m, expr const & t) {
    assign(m, t, justification());
}

void substitution::assign(name const & m, level const & l, justification const & j) {
    m_level_subst.insert(m, mk_pair(l, j));
}

void substitution::assign(name const & m, level const & l) {
    assign(m, l, justification());
}

void substitution::for_each(std::function<void(name const & n, expr const & e, justification const & j)> const & fn) const {
    m_expr_subst.for_each([=](name const & n, std::pair<expr, justification> const & a) {
            fn(n, a.first, a.second);
        });
}

void substitution::for_each(std::function<void(name const & n, level const & e, justification const & j)> const & fn) const {
    m_level_subst.for_each([=](name const & n, std::pair<level, justification> const & a) {
            fn(n, a.first, a.second);
        });
}

std::pair<level, justification> instantiate_metavars(level const & l, substitution & s, bool use_jst, bool updt) {
    if (!has_param(l))
        return mk_pair(l, justification());
    justification j;
    auto save_jst = [&](justification const & j2) { j = mk_composite1(j, j2); };
    level r = replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_meta(l)) {
                auto p1 = s.get_assignment(l);
                if (p1) {
                    auto p2 = instantiate_metavars(p1->first, s, use_jst, updt);
                    if (use_jst) {
                        justification new_jst = mk_composite1(p1->second, p2.second);
                        if (updt)
                            s.assign(l, p2.first, new_jst);
                        save_jst(new_jst);
                    } else if (updt) {
                        s.assign(l, p2.first);
                    }
                    return some_level(p2.first);
                }
            }
            return none_level();
        });
    return mk_pair(r, j);
}

class instantiate_metavars_fn : public replace_visitor {
protected:
    substitution & m_subst;
    justification  m_jst;
    bool           m_use_jst;
    bool           m_update;

    void save_jst(justification const & j) { m_jst = mk_composite1(m_jst, j); }

    level visit_level(level const & l) {
        auto p1 = instantiate_metavars(l, m_subst, m_use_jst, m_update);
        if (m_use_jst)
            save_jst(p1.second);
        return p1.first;
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls, [&](level const & l) { return visit_level(l); }, [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s, context const &) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c, context const &) {
        return update_constant(c, visit_levels(const_level_params(c)));
    }

    virtual expr visit_meta(expr const & m, context const &) {
        name const & m_name = mlocal_name(m);
        auto p1 = m_subst.get_expr_assignment(m_name);
        if (p1) {
            if (!has_metavar(p1->first)) {
                if (m_use_jst)
                    save_jst(p1->second);
                return p1->first;
            } else if (m_use_jst) {
                if (m_update) {
                    auto p2 = m_subst.d_instantiate_metavars(p1->first);
                    justification new_jst = mk_composite1(p1->second, p2.second);
                    m_subst.assign(m_name, p2.first, new_jst);
                    save_jst(new_jst);
                    return p2.first;
                } else {
                    auto p2 = m_subst.instantiate_metavars(p1->first);
                    save_jst(mk_composite1(p1->second, p2.second));
                    return p2.first;
                }
            } else {
                if (m_update) {
                    expr r = m_subst.d_instantiate_metavars_wo_jst(p1->first);
                    m_subst.assign(m_name, r);
                    return r;
                } else {
                    return m_subst.instantiate_metavars_wo_jst(p1->first);
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
        if (is_metavar(f) && m_subst.is_expr_assigned(mlocal_name(f))) {
            expr new_f = visit_meta(f, ctx);
            return apply_beta(new_f, args.size(), args.data());
        } else {
            args.push_back(visit(f, ctx));
            return update_rev_app(e, args);
        }
    }

    virtual expr visit(expr const & e, context const & ctx) {
        if (!has_metavar(e)) {
            return e;
        } else {
            return replace_visitor::visit(e, ctx);
        }
    }

public:
    instantiate_metavars_fn(substitution & s, bool use_jst, bool updt):
        m_subst(s), m_use_jst(use_jst), m_update(updt) {}
    justification const & get_justification() const { return m_jst; }
};

std::pair<expr, justification> substitution::instantiate_metavars(expr const & e) const {
    instantiate_metavars_fn fn(const_cast<substitution&>(*this), true, false);
    expr r = fn(e);
    return mk_pair(r, fn.get_justification());
}

std::pair<expr, justification> substitution::d_instantiate_metavars(expr const & e) {
    instantiate_metavars_fn fn(*this, true, true);
    expr r = fn(e);
    return mk_pair(r, fn.get_justification());
}

expr substitution::instantiate_metavars_wo_jst(expr const & e) const {
    return instantiate_metavars_fn(const_cast<substitution&>(*this), false, false)(e);
}

expr substitution::d_instantiate_metavars_wo_jst(expr const & e) {
    return instantiate_metavars_fn(*this, false, true)(e);
}

bool substitution::occurs_expr(name const & m, expr const & e) const {
    if (!has_metavar(e))
        return false;
    auto it = find(e, [&](expr const & e, unsigned) {
            if (is_metavar(e)) {
                if (mlocal_name(e) == m)
                    return true;
                auto s = get_expr(e);
                return s && occurs_expr(m, *s);
            } else {
                return false;
            }
        });
    return static_cast<bool>(it);
}
}
