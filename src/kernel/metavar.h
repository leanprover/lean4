/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/rb_map.h"
#include "util/optional.h"
#include "kernel/expr.h"
#include "kernel/justification.h"

namespace lean {
class substitution {
    rb_map<name, std::pair<expr, justification>, name_quick_cmp> m_subst;
public:
    bool is_assigned(name const & m) const;
    optional<std::pair<expr, justification>> get_assignment(name const & m) const;
    optional<expr> get_expr(name const & m) const;
    void assign(name const & m, expr const & t, justification const & j);
    void assign(name const & m, expr const & t);
    void for_each(std::function<void(name const & n, expr const & e, justification const & j)> const & fn);
};
/**
   \brief Instantiate metavariables in \c e assigned in the substitution \c s.
*/
std::pair<expr, justification> instantiate_metavars(expr const & e, substitution const & s);
/**
   \brief Similar to the previous function, but it compress the substitution.
   By compress, we mean, for any metavariable \c m reachable from \c e,
   if s[m] = t, and t has asssigned metavariables, then s[m] <- instantiate_metavars(t, s).
*/
std::pair<expr, justification> d_instantiate_metavars(expr const & e, substitution & s);
/**
   \brief Instantiate metavariables in \c e assigned in the substitution \c s,
   but does not return a justification object for the new expression.
*/
expr instantiate_metavars_wo_jst(expr const & e, substitution const & s);
}
