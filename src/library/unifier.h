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
#include "util/sexpr/options.h"
#include "kernel/constraint.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"

#ifndef LEAN_DEFAULT_UNIFIER_MAX_STEPS
#define LEAN_DEFAULT_UNIFIER_MAX_STEPS 10000
#endif

namespace lean {
unsigned get_unifier_max_steps(options const & opts);
bool get_unifier_use_exceptions(options const & opts);

bool is_simple_meta(expr const & e);

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
                              unifier_plugin const & p, bool use_exception = true, unsigned max_steps = LEAN_DEFAULT_UNIFIER_MAX_STEPS);
lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception = true, unsigned max_steps = LEAN_DEFAULT_UNIFIER_MAX_STEPS);
lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              unifier_plugin const & p, options const & o);
lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              options const & o);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p,
                              substitution const & s = substitution(), unsigned max_steps = LEAN_DEFAULT_UNIFIER_MAX_STEPS);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen,
                              substitution const & s = substitution(), unsigned max_steps = LEAN_DEFAULT_UNIFIER_MAX_STEPS);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p,
                              substitution const & s, options const & o);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen,
                              substitution const & s, options const & o);

class unifier_exception : public exception {
    justification m_jst;
    substitution  m_subst;
public:
    unifier_exception(justification const & j, substitution const & s):exception("unifier exception"), m_jst(j), m_subst(s) {}
    virtual exception * clone() const { return new unifier_exception(m_jst, m_subst); }
    virtual void rethrow() const { throw *this; }
    justification const & get_justification() const { return m_jst; }
    substitution const & get_substitution() const { return m_subst; }
};

void open_unifier(lua_State * L);
}
