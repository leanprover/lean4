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

    std::pair<expr, justification> d_instantiate_metavars(expr const & e, name_set * unassigned_lvls, name_set * unassigned_exprs);
    expr d_instantiate_metavars_wo_jst(expr const & e);
    std::pair<level, justification> d_instantiate_metavars(level const & l, bool use_jst, bool updt, name_set * unassigned);
    friend class instantiate_metavars_fn;

    justification get_expr_jst(name const & m) const { if (auto it = m_expr_jsts.find(m)) return *it; else return justification(); }
    justification get_level_jst(name const & m) const { if (auto it = m_level_jsts.find(m)) return *it; else return justification(); }

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

    substitution assign(name const & m, expr const & t, justification const & j) const;
    substitution assign(name const & m, expr const & t) const;

    substitution assign(name const & m, level const & t, justification const & j) const;
    substitution assign(name const & m, level const & t) const;

    void d_assign(name const & m, expr const & t, justification const & j);
    void d_assign(name const & m, expr const & t) { d_assign(m, t, justification()); }
    void d_assign(expr const & m, expr const & t, justification const & j) { d_assign(mlocal_name(m), t, j); }
    void d_assign(expr const & m, expr const & t) { d_assign(m, t, justification()); }
    void d_assign(name const & m, level const & t, justification const & j);
    void d_assign(name const & m, level const & t) { d_assign(m, t, justification ()); }
    void d_assign(level const & m, level const & t, justification const & j) { d_assign(meta_id(m), t, j); }
    void d_assign(level const & m, level const & t) { d_assign(m, t, justification ()); }

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
    substitution assign(expr const & m, expr const & t, justification const & j) { lean_assert(is_metavar(m)); return assign(mlocal_name(m), t, j); }
    substitution assign(expr const & m, expr const & t) const { lean_assert(is_metavar(m)); return assign(mlocal_name(m), t); }

    bool is_assigned(level const & m) const { lean_assert(is_meta(m)); return is_level_assigned(meta_id(m)); }
    opt_level_jst get_assignment(level const & m) const { lean_assert(is_meta(m)); return get_level_assignment(meta_id(m)); }
    optional<level> get_level(level const & m) const { lean_assert(is_meta(m)); return get_level(meta_id(m)); }
    substitution assign(level const & m, level const & l, justification const & j) const { lean_assert(is_meta(m)); return assign(meta_id(m), l, j); }
    substitution assign(level const & m, level const & l) { lean_assert(is_meta(m)); return assign(meta_id(m), l); }

    /**
        \brief Instantiate metavariables in \c e assigned in this substitution.

        \remark If \c unassigned_exprs and \c unassigned_lvls are not nullptr, then this method
        stores unassigned metavariables in them.
    */
    std::pair<expr, justification> instantiate_metavars(expr const & e, name_set * unassigned_lvls = nullptr,
                                                        name_set * unassigned_exprs = nullptr) const;

    /**
       \brief Similar to the previous function, but it compress the substitution.
       By compress, we mean, for any metavariable \c m reachable from \c e,
       if s[m] = t, and t has asssigned metavariables, then s[m] <- instantiate_metavars(t, s).
       The updated substitution is returned.
    */
    std::tuple<expr, justification, substitution> updt_instantiate_metavars(expr const & e, name_set * unassigned_lvls = nullptr,
                                                                            name_set * unassigned_exprs = nullptr) const;

    /**
        \brief Instantiate level metavariables in \c l.

        \remark If \c unassigned is not nullptr, then store unassigned meta universe parameters in it.
    */
    std::pair<level, justification> instantiate_metavars(level const & l, name_set * unassigned = nullptr) const;

    /**
       \brief Instantiate metavariables in \c e assigned in the substitution \c s,
       but does not return a justification object for the new expression.
    */
    expr instantiate_metavars_wo_jst(expr const & e) const;
    expr instantiate(expr const & e) const { return instantiate_metavars_wo_jst(e); }

    std::pair<expr, substitution> updt_instantiate_metavars_wo_jst(expr const & e) const;

    /** \brief Instantiate level metavariables in \c l, but does not return justification object. */
    level instantiate_metavars_wo_jst(level const & l) const;

    /** \brief Return true iff the metavariable \c m occurrs (directly or indirectly) in \c e. */
    bool occurs_expr(name const & m, expr const & e) const;
    bool occurs(expr const & m, expr const & e) const { lean_assert(is_metavar(m)); return occurs_expr(mlocal_name(m), e); }
};
}
