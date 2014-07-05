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

#ifndef LEAN_DEFAULT_UNIFIER_UNFOLD_OPAQUE
#define LEAN_DEFAULT_UNIFIER_UNFOLD_OPAQUE false
#endif

namespace lean {
unsigned get_unifier_max_steps(options const & opts);
bool get_unifier_unfold_opaque(options const & opts);

bool is_simple_meta(expr const & e);
expr mk_aux_metavar_for(name_generator & ngen, expr const & t);

enum class unify_status { Solved, Failed, Unsupported };
/**
    \brief Handle the easy-cases: first-order unification, higher-order patterns, identical terms, and terms without metavariables.

    This function assumes that all assigned metavariables have been substituted.
*/
std::pair<unify_status, substitution> unify_simple(substitution const & s, expr const & lhs, expr const & rhs, justification const & j);
std::pair<unify_status, substitution> unify_simple(substitution const & s, level const & lhs, level const & rhs, justification const & j);
std::pair<unify_status, substitution> unify_simple(substitution const & s, constraint const & c);

lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception = true, unsigned max_steps = LEAN_DEFAULT_UNIFIER_MAX_STEPS,
                              bool unfold_opaque = LEAN_DEFAULT_UNIFIER_UNFOLD_OPAQUE);
lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception, options const & o);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen,
                              substitution const & s = substitution(), unsigned max_steps = LEAN_DEFAULT_UNIFIER_MAX_STEPS,
                              bool unfold_opaque = LEAN_DEFAULT_UNIFIER_UNFOLD_OPAQUE);
lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, substitution const & s,
                              options const & o);

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
