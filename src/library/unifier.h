/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <functional>
#include "util/lua.h"
#include "util/lazy_list.h"
#include "util/name_generator.h"
#include "kernel/constraint.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"

namespace lean {
enum class unify_status { Solved, Failed, Unsupported };
/**
    \brief Handle the easy-cases: first-order unification, higher-order patterns, identical terms, and terms without metavariables.

    This function assumes that all assigned metavariables have been substituted.
*/
std::pair<unify_status, substitution> unify_simple(substitution const & s, expr const & lhs, expr const & rhs, justification const & j);
std::pair<unify_status, substitution> unify_simple(substitution const & s, level const & lhs, level const & rhs, justification const & j);
std::pair<unify_status, substitution> unify_simple(substitution const & s, constraint const & c);

/**
   \brief A unifier_plugin provides a simple way to extend the \c unify procedures.
   Whenever, the default implementation does not know how to solve a constraint, it invokes the plugin.
   The plugin return a lazy_list (stream) of possible solutions. Each "solution" is represented as
   a new list of constraints.
*/
typedef std::function<lazy_list<constraints>(constraint const &, name_generator const &)> unifier_plugin;

lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              unifier_plugin const & p, bool use_exception = true);
lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception = true);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen);

void open_unifier(lua_State * L);
}
