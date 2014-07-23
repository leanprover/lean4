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
substitution::substitution() {}

bool substitution::is_expr_assigned(name const & m) const {
    return m_expr_subst.contains(m);
}

auto substitution::get_expr_assignment(name const & m) const -> opt_expr_jst {
    auto it = m_expr_subst.find(m);
    if (it)
        return opt_expr_jst(mk_pair(*it, get_expr_jst(m)));
    else
        return opt_expr_jst();
}

bool substitution::is_level_assigned(name const & m) const {
    return m_level_subst.contains(m);
}

auto substitution::get_level_assignment(name const & m) const -> opt_level_jst {
    auto it = m_level_subst.find(m);
    if (it)
        return opt_level_jst(mk_pair(*it, get_level_jst(m)));
    else
        return opt_level_jst();
}

optional<expr> substitution::get_expr(name const & m) const {
    auto it = m_expr_subst.find(m);
    return it ? some_expr(*it) : none_expr();
}

optional<level> substitution::get_level(name const & m) const {
    auto it = m_level_subst.find(m);
    return it ? some_level(*it) : none_level();
}

void substitution::d_assign(name const & m, expr const & t, justification const & j) {
    lean_assert(closed(t));
    m_expr_subst.insert(m, t);
    if (!j.is_none())
        m_expr_jsts.insert(m, j);
}

void substitution::d_assign(name const & m, level const & l, justification const & j) {
    m_level_subst.insert(m, l);
    if (!j.is_none())
        m_level_jsts.insert(m, j);
}

substitution substitution::assign(name const & m, expr const & t, justification const & j) const {
    substitution s(*this);
    s.d_assign(m, t, j);
    return s;
}

substitution substitution::assign(name const & m, expr const & t) const {
    return assign(m, t, justification());
}

substitution substitution::assign(name const & m, level const & l, justification const & j) const {
    substitution s(*this);
    s.d_assign(m, l, j);
    return s;
}

substitution substitution::assign(name const & m, level const & l) const {
    return assign(m, l, justification());
}

std::pair<level, justification> substitution::d_instantiate_metavars(level const & l, bool use_jst, bool updt) {
    if (!has_meta(l))
        return mk_pair(l, justification());
    justification j;
    auto save_jst = [&](justification const & j2) { j = mk_composite1(j, j2); };
    level r = replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_meta(l)) {
                auto p1 = get_assignment(l);
                if (p1) {
                    auto p2 = d_instantiate_metavars(p1->first, use_jst, updt);
                    if (use_jst) {
                        justification new_jst = mk_composite1(p1->second, p2.second);
                        if (updt)
                            d_assign(meta_id(l), p2.first, new_jst);
                        save_jst(new_jst);
                    } else if (updt) {
                        d_assign(meta_id(l), p2.first);
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
    bool           m_only_expr;

    void save_jst(justification const & j) { m_jst = mk_composite1(m_jst, j); }

    level visit_level(level const & l) {
        auto p1 = m_subst.d_instantiate_metavars(l, m_use_jst, m_update);
        if (m_use_jst)
            save_jst(p1.second);
        return p1.first;
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls, [&](level const & l) { return visit_level(l); }, [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) {
        lean_assert(!m_only_expr);
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) {
        lean_assert(!m_only_expr);
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_meta(expr const & m) {
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
                    m_subst.d_assign(m_name, p2.first, new_jst);
                    save_jst(new_jst);
                    return p2.first;
                } else {
                    auto p2 = m_subst.instantiate_metavars(p1->first);
                    save_jst(mk_composite1(p1->second, p2.second));
                    return p2.first;
                }
            } else {
                if (m_update) {
                    auto p2 = m_subst.d_instantiate_metavars(p1->first);
                    m_subst.d_assign(m_name, p2.first, mk_composite1(p1->second, p2.second));
                    return p2.first;
                } else {
                    return m_subst.instantiate(p1->first);
                }
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const * it = &e;
        while (is_app(*it)) {
            args.push_back(visit(app_arg(*it)));
            it = &app_fn(*it);
        }
        expr const & f = *it;
        if (is_metavar(f) && m_subst.is_expr_assigned(mlocal_name(f))) {
            expr new_f = visit_meta(f);
            return apply_beta(new_f, args.size(), args.data());
        } else {
            args.push_back(visit(f));
            return update_rev_app(e, args);
        }
    }

    virtual expr visit(expr const & e) {
        if ((m_only_expr && !has_expr_metavar(e)) || (!m_only_expr && !has_metavar(e))) {
            return e;
        } else {
            return replace_visitor::visit(e);
        }
    }

public:
    instantiate_metavars_fn(substitution & s, bool use_jst, bool updt, bool only_expr = false):
        m_subst(s), m_use_jst(use_jst), m_update(updt), m_only_expr(only_expr) {}
    justification const & get_justification() const { return m_jst; }
};

std::pair<expr, justification> substitution::instantiate_metavars(expr const & e) const {
    substitution s(*this);
    instantiate_metavars_fn fn(s, true, false);
    expr r = fn(e);
    return mk_pair(r, fn.get_justification());
}

std::pair<expr, justification> substitution::d_instantiate_metavars(expr const & e, bool only_expr) {
    if ((only_expr && !has_expr_metavar(e)) || (!only_expr && !has_metavar(e))) {
        return mk_pair(e, justification());
    } else {
        instantiate_metavars_fn fn(*this, true, true, only_expr);
        expr r = fn(e);
        return mk_pair(r, fn.get_justification());
    }
}

std::tuple<expr, justification, substitution> substitution::updt_instantiate_metavars(expr const & e) const {
    substitution s(*this);
    instantiate_metavars_fn fn(s, true, true);
    expr r = fn(e);
    return std::make_tuple(r, fn.get_justification(), s);
}

std::pair<level, justification> substitution::instantiate_metavars(level const & l) const {
    substitution s(*this);
    return s.d_instantiate_metavars(l, true, false);
}

expr substitution::instantiate_metavars_wo_jst(expr const & e) const {
    substitution s(*this);
    return instantiate_metavars_fn(s, false, false)(e);
}

expr substitution::d_instantiate_metavars_wo_jst(expr const & e) {
    return instantiate_metavars_fn(*this, false, true)(e);
}

std::pair<expr, substitution> substitution::updt_instantiate_metavars_wo_jst(expr const & e) const {
    substitution s(*this);
    return mk_pair(instantiate_metavars_fn(s, false, true)(e), s);
}

level substitution::instantiate_metavars_wo_jst(level const & l) const {
    substitution s(*this);
    return s.d_instantiate_metavars(l, false, false).first;
}

bool substitution::occurs_expr(name const & m, expr const & e) const {
    if (!has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e)) return false;
            if (is_metavar(e)) {
                if (mlocal_name(e) == m)
                    found = true;
                auto s = get_expr(e);
                if (s && occurs_expr(m, *s))
                    found = true;
                return false; // do not visit type
            }
            if (is_local(e)) return false; // do not visit type
            return true;
        });
    return found;
}
}
