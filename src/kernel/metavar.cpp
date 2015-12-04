/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/interrupt.h"
#include "kernel/metavar.h"
#include "kernel/free_vars.h"
#include "kernel/justification.h"
#include "kernel/instantiate.h"
#include "kernel/find_fn.h"
#include "kernel/expr_maps.h"
#include "kernel/level.h"
#include "kernel/cache_stack.h"
#include "kernel/expr_cache.h"
#include "kernel/abstract.h"

#ifndef LEAN_INSTANTIATE_METAVARS_CACHE_CAPACITY
#define LEAN_INSTANTIATE_METAVARS_CACHE_CAPACITY 1024*8
#endif

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

void substitution::assign(expr const & mvar, buffer<expr> const & locals, expr const & v, justification const & j) {
    lean_assert(mvar != v);
    assign(mlocal_name(mvar), Fun(locals, v), j);
}

void substitution::assign(name const & m, expr const & t, justification const & j) {
    lean_assert(closed(t));
    lean_assert(!is_metavar(t) || m != mlocal_name(t));
    m_expr_subst.insert(m, t);
    m_occs_map.erase(m);
    if (!j.is_none())
        m_expr_jsts.insert(m, j);
}

void substitution::assign(name const & m, level const & l, justification const & j) {
    lean_assert(!::lean::occurs(mk_meta_univ(m), l), m, l);
    m_level_subst.insert(m, l);
    if (!j.is_none())
        m_level_jsts.insert(m, j);
}

pair<level, justification> substitution::instantiate_metavars(level const & l, bool use_jst) {
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

typedef expr_cache instantiate_metavars_cache;
MK_CACHE_STACK(instantiate_metavars_cache, LEAN_INSTANTIATE_METAVARS_CACHE_CAPACITY)

class instantiate_metavars_fn {
protected:
    typedef instantiate_metavars_cache_ref cache_ref;
    substitution & m_subst;
    cache_ref      m_cache;
    justification  m_jst;
    bool           m_use_jst;
    // if m_inst_local_types, then instantiate metavariables nested in the types of local constants and metavariables.
    bool           m_inst_local_types;

    void save_jst(justification const & j) { m_jst = mk_composite1(m_jst, j); }

    level visit_level(level const & l) {
        auto p1 = m_subst.instantiate_metavars(l, m_use_jst);
        if (m_use_jst)
            save_jst(p1.second);
        return p1.first;
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    expr visit_sort(expr const & s) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    expr visit_constant(expr const & c) {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    expr visit_meta(expr const & m) {
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
            if (m_inst_local_types)
                return update_mlocal(m, visit(mlocal_type(m)));
            else
                return m;
        }
    }

    expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (is_metavar(f)) {
            if (auto p1 = m_subst.get_expr_assignment(mlocal_name(f))) {
                if (m_use_jst)
                    save_jst(p1->second);
                expr new_app = apply_beta(p1->first, args.size(), args.data());
                return visit(new_app);
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

    expr save_result(expr const & e, expr && r) {
        m_cache->insert(e, r);
        return r;
    }

    expr visit_macro(expr const & e) {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    expr visit_binding(expr const & e) {
        lean_assert(is_binding(e));
        expr new_d = visit(binding_domain(e));
        expr new_b = visit(binding_body(e));
        return update_binding(e, new_d, new_b);
    }

    expr visit(expr const & e) {
        if (!has_metavar(e))
            return e;
        check_system("instantiate metavars");

        if (auto it = m_cache->find(e))
            return *it;

        switch (e.kind()) {
        case expr_kind::Sort:      return save_result(e, visit_sort(e));
        case expr_kind::Var:       lean_unreachable();
        case expr_kind::Local:
            if (m_inst_local_types)
                return save_result(e, update_mlocal(e, visit(mlocal_type(e))));
            else
                return e;
        case expr_kind::Constant:  return save_result(e, visit_constant(e));
        case expr_kind::Macro:     return save_result(e, visit_macro(e));
        case expr_kind::Meta:      return save_result(e, visit_meta(e));
        case expr_kind::App:       return save_result(e, visit_app(e));
        case expr_kind::Lambda:
        case expr_kind::Pi:        return save_result(e, visit_binding(e));
        }
        lean_unreachable();
    }

public:
    instantiate_metavars_fn(substitution & s, bool use_jst, bool inst_local_types):
        m_subst(s), m_use_jst(use_jst), m_inst_local_types(inst_local_types) {}
    justification const & get_justification() const { return m_jst; }
    expr operator()(expr const & e) { return visit(e); }
};

pair<expr, justification> substitution::instantiate_metavars_core(expr const & e, bool inst_local_types) {
    if (!has_metavar(e)) {
        return mk_pair(e, justification());
    } else {
        instantiate_metavars_fn fn(*this, true, inst_local_types);
        expr r = fn(e);
        return mk_pair(r, fn.get_justification());
    }
}

expr substitution::instantiate_metavars_wo_jst(expr const & e, bool inst_local_types) {
    return instantiate_metavars_fn(*this, false, inst_local_types)(e);
}

auto substitution::expand_metavar_app(expr const & e) -> opt_expr_jst {
    expr const & f = get_app_fn(e);
    if (!is_metavar(f))
        return opt_expr_jst();
    name const & f_name = mlocal_name(f);
    auto f_value = get_expr(f_name);
    if (!f_value)
        return opt_expr_jst();
    buffer<expr> args;
    get_app_rev_args(e, args);
    lean_assert(*f_value != f);
    expr new_e = apply_beta(*f_value, args.size(), args.data());
    return opt_expr_jst(new_e, get_expr_jst(f_name));
}

static name_set merge(name_set s1, name_set const & s2) {
    s2.for_each([&](name const & n) { s1.insert(n); });
    return s1;
}

static bool all_unassigned(substitution const & subst, name_set const & s) {
    return !s.find_if([&](name const & m) { return subst.is_expr_assigned(m); });
}

name_set substitution::get_occs(name const & m, name_set & fresh) {
    lean_assert(is_expr_assigned(m));
    check_system("substitution occurs check");
    if (fresh.contains(m)) {
        return *m_occs_map.find(m);
    } else if (name_set const * it = m_occs_map.find(m)) {
        name_set curr_occs = *it;
        if (all_unassigned(*this, curr_occs)) {
            return curr_occs;
        }
        name_set new_occs;
        curr_occs.for_each([&](name const & n) {
                if (is_expr_assigned(n)) {
                    new_occs = merge(new_occs, get_occs(n, fresh));
                } else {
                    // we need to update
                    new_occs.insert(n);
                }
            });
        m_occs_map.insert(m, new_occs);
        fresh.insert(m);
        return new_occs;
    } else {
        expr e = *get_expr(m);
        name_set occs;
        ::lean::for_each(e, [&](expr const & e, unsigned) {
                if (!has_expr_metavar(e)) return false;
                if (is_local(e)) return false; // do not process type
                if (is_metavar(e)) {
                    name const & n = mlocal_name(e);
                    if (is_expr_assigned(n)) {
                        occs = merge(occs, get_occs(n, fresh));
                    } else {
                        occs.insert(n);
                    }
                    return false;
                }
                return true;
            });
        m_occs_map.insert(m, occs);
        fresh.insert(m);
        return occs;
    }
}

bool substitution::occurs_expr(name const & m, expr const & e) {
    if (!has_expr_metavar(e))
        return false;
    name_set fresh;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e)) return false;
            if (is_metavar(e)) {
                name const & n = mlocal_name(e);
                if (is_expr_assigned(n)) {
                    if (get_occs(n, fresh).contains(m))
                        found = true;
                } else if (n == m) {
                    found = true;
                }
                return false; // do not visit type
            }
            if (is_local(e)) return false; // do not visit type
            return true;
        });
    return found;
}
}
