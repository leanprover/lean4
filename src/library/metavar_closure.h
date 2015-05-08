/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_tree.h"
#include "kernel/metavar.h"
#include "library/expr_lt.h"

namespace lean {
/** \brief Helper object for collecting metavariables occurring in expressions.
    It also provides a method that given a substitution \c s, produces a constraint
           ?m =?= s(?m)
    for each collected metavariable ?m that is assigned in \c s.

    \remark Metavariables occuring in the type of other metavariables are ignored.
*/
class metavar_closure {
    rb_tree<expr, expr_quick_cmp>   m_expr_mvars;
    rb_tree<level, level_quick_cmp> m_lvl_mvars;
 public:
    metavar_closure() {}
    metavar_closure(expr const & e) { add(e); }
    /** \brief Collect metavariables occurring in \c e */
    void add(expr const & e);
    void add(level const & l);
    /** \brief Execute \c fn for each collected metavariable */
    void for_each_expr_mvar(std::function<void(expr const &)> const & fn) const;
    void for_each_level_mvar(std::function<void(level const &)> const & fn) const;
    /** \brief For each collected metavariable ?m, store in \c r constraints of the form ?m =?= s(?m)
        if ?m is assigned by \c s. The constraints are justified by \c j
        \see mk_eq_cnstr
    */
    void mk_constraints(substitution s, justification const & j, buffer<constraint> & r) const;
    constraints mk_constraints(substitution s, justification const & j) const;
};
}
