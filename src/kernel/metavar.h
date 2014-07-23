/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/rb_map.h"
#include "util/optional.h"
#include "util/name_set.h"
#include "kernel/expr.h"
#include "kernel/justification.h"

namespace lean {
class substitution {
    typedef rb_map<name, expr, name_quick_cmp>          expr_map;
    typedef rb_map<name, level, name_quick_cmp>         level_map;
    typedef rb_map<name, justification, name_quick_cmp> jst_map;

    expr_map  m_expr_subst;
    level_map m_level_subst;
    jst_map   m_expr_jsts;
    jst_map   m_level_jsts;

    friend class instantiate_metavars_fn;
    std::pair<level, justification> instantiate_metavars(level const & l, bool use_jst);
    expr instantiate_metavars_wo_jst(expr const & e);
    bool occurs_expr_core(name const & m, expr const & e, name_set & visited) const;

public:
    substitution();
    typedef optional<std::pair<expr,  justification>> opt_expr_jst;
    typedef optional<std::pair<level, justification>> opt_level_jst;

    bool is_expr_assigned(name const & m) const;
    opt_expr_jst get_expr_assignment(name const & m) const;

    bool is_level_assigned(name const & m) const;
    opt_level_jst get_level_assignment(name const & m) const;

    optional<expr> get_expr(name const & m) const;
    optional<level> get_level(name const & m) const;
    justification get_expr_jst(name const & m) const { if (auto it = m_expr_jsts.find(m)) return *it; else return justification(); }
    justification get_level_jst(name const & m) const { if (auto it = m_level_jsts.find(m)) return *it; else return justification(); }

    void assign(name const & m, expr const & t, justification const & j);
    void assign(name const & m, expr const & t) { assign(m, t, justification()); }
    void assign(expr const & m, expr const & t, justification const & j) { assign(mlocal_name(m), t, j); }
    void assign(expr const & m, expr const & t) { assign(m, t, justification()); }
    void assign(name const & m, level const & t, justification const & j);
    void assign(name const & m, level const & t) { assign(m, t, justification ()); }
    void assign(level const & m, level const & t, justification const & j) { assign(meta_id(m), t, j); }
    void assign(level const & m, level const & t) { assign(m, t, justification ()); }

    std::pair<expr, justification> instantiate_metavars(expr const & e);
    std::pair<level, justification> instantiate_metavars(level const & l) { return instantiate_metavars(l, true); }

    void forget_justifications() { m_expr_jsts  = jst_map(); m_level_jsts = jst_map(); }

    template<typename F>
    void for_each_expr(F && fn) const {
        for_each(m_expr_subst, [=](name const & n, expr const & e) { fn(n, e, get_expr_jst(n)); });
    }

    template<typename F>
    void for_each_level(F && fn) const {
        for_each(m_level_subst, [=](name const & n, level const & l) { fn(n, l, get_level_jst(n)); });
    }

    bool is_assigned(expr const & m) const { lean_assert(is_metavar(m)); return is_expr_assigned(mlocal_name(m)); }
    opt_expr_jst get_assignment(expr const & m) const { lean_assert(is_metavar(m)); return get_expr_assignment(mlocal_name(m)); }
    optional<expr> get_expr(expr const & m) const { lean_assert(is_metavar(m)); return get_expr(mlocal_name(m)); }

    bool is_assigned(level const & m) const { lean_assert(is_meta(m)); return is_level_assigned(meta_id(m)); }
    opt_level_jst get_assignment(level const & m) const { lean_assert(is_meta(m)); return get_level_assignment(meta_id(m)); }
    optional<level> get_level(level const & m) const { lean_assert(is_meta(m)); return get_level(meta_id(m)); }

    expr instantiate(expr const & e) { return instantiate_metavars_wo_jst(e); }

    /** \brief Return true iff the metavariable \c m occurrs (directly or indirectly) in \c e. */
    bool occurs_expr(name const & m, expr const & e) const;
    bool occurs(expr const & m, expr const & e) const { lean_assert(is_metavar(m)); return occurs_expr(mlocal_name(m), e); }
};
}
