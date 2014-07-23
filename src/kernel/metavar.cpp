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

void substitution::assign(name const & m, expr const & t, justification const & j) {
    lean_assert(closed(t));
    m_expr_subst.insert(m, t);
    if (!j.is_none())
        m_expr_jsts.insert(m, j);
}

void substitution::assign(name const & m, level const & l, justification const & j) {
    m_level_subst.insert(m, l);
    if (!j.is_none())
        m_level_jsts.insert(m, j);
}

std::pair<level, justification> substitution::instantiate_metavars(level const & l, bool use_jst) {
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
                    auto p2 = instantiate_metavars(p1->first, use_jst);
                    if (use_jst) {
                        justification new_jst = mk_composite1(p1->second, p2.second);
                        assign(meta_id(l), p2.first, new_jst);
                        save_jst(new_jst);
                    } else {
                        assign(meta_id(l), p2.first);
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

    void save_jst(justification const & j) { m_jst = mk_composite1(m_jst, j); }

    level visit_level(level const & l) {
        auto p1 = m_subst.instantiate_metavars(l, m_use_jst);
        if (m_use_jst)
            save_jst(p1.second);
        return p1.first;
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls, [&](level const & l) { return visit_level(l); }, [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) {
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
                auto p2 = m_subst.instantiate_metavars(p1->first);
                justification new_jst = mk_composite1(p1->second, p2.second);
                m_subst.assign(m_name, p2.first, new_jst);
                save_jst(new_jst);
                return p2.first;
            } else {
                auto p2 = m_subst.instantiate_metavars(p1->first);
                m_subst.assign(m_name, p2.first, mk_composite1(p1->second, p2.second));
                return p2.first;
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
        if (!has_metavar(e)) {
            return e;
        } else {
            return replace_visitor::visit(e);
        }
    }

public:
    instantiate_metavars_fn(substitution & s, bool use_jst):
        m_subst(s), m_use_jst(use_jst) {}
    justification const & get_justification() const { return m_jst; }
};

std::pair<expr, justification> substitution::instantiate_metavars(expr const & e) {
    if (!has_metavar(e)) {
        return mk_pair(e, justification());
    } else {
        instantiate_metavars_fn fn(*this, true);
        expr r = fn(e);
        return mk_pair(r, fn.get_justification());
    }
}

expr substitution::instantiate_metavars_wo_jst(expr const & e) {
    return instantiate_metavars_fn(*this, false)(e);
}


bool substitution::occurs_expr_core(name const & m, expr const & e, name_set & visited) const {
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e)) return false;
            if (is_metavar(e)) {
                name const & n = mlocal_name(e);
                if (n == m)
                    found = true;
                auto s = get_expr(e);
                if (!s || visited.contains(n))
                    return false; // do not visit type
                visited.insert(n);
                if (s && occurs_expr_core(m, *s, visited))
                    found = true;
                return false; // do not visit type
            }
            if (is_local(e)) return false; // do not visit type
            return true;
        });
    return found;
}

bool substitution::occurs_expr(name const & m, expr const & e) const {
    if (!has_expr_metavar(e))
        return false;
    name_set visited;
    return occurs_expr_core(m, e, visited);
}
}
