/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lazy_list.h"
#include "kernel/environment.h"
#include "kernel/constraint.h"
#include "kernel/type_checker.h"

namespace lean {
/**
   \brief A unifier_plugin provides a simple way to extend the \c unify procedures.
   Whenever, the default implementation does not know how to solve a constraint, it invokes the plugin.
   The plugin return a lazy_list (stream) of possible solutions. Each "solution" is represented as
   a new list of constraints.

   The method \c delay_constraint is invoked to decide whether the particular constraint should
   be delayed. This is useful when implementing unification plugins
*/
class unifier_plugin_cell {
public:
    virtual ~unifier_plugin_cell() {}
    virtual lazy_list<constraints> solve(type_checker &, constraint const &, name_generator &&) const = 0;
    virtual bool delay_constraint(type_checker &, constraint const &) const = 0;
};

typedef std::shared_ptr<unifier_plugin_cell> unifier_plugin;
/** \brief Combine two plugins by appending their solutions. */
unifier_plugin append(unifier_plugin const & p1, unifier_plugin const & p2);
/** \brief Combine two plugins by taking the solutions of p1, if it is empty, then return solutions of p2 */
unifier_plugin orelse(unifier_plugin const & p1, unifier_plugin const & p2);

environment set_unifier_plugin(environment const & env, unifier_plugin const & p);
unifier_plugin const & get_unifier_plugin(environment const & env);
void initialize_unifier_plugin();
void finalize_unifier_plugin();
}
