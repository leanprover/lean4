/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"
#include "library/expr_pair.h"
namespace lean {
/**
   \brief Given a proposition \c e and its proof H, return a list of conditional equations (and proofs) extracted from \c e.

   The following rules are used to convert \c e into conditional equations.

   [not P]              --->   P = false
   [P /\ Q]             --->   [P], [Q]
   [if P then Q else R] --->   P -> [Q],  not P -> [Q]
   [P -> Q]             --->   P -> [Q]
   [forall x : A, P]    --->   forall x : A, [P]
   [a ≠ b]              --->   (a = b) = false

   P                    --->   P = true   (if none of the rules above apply and P is not an equality)

   \remark if the left-hand-side of an equation does not contain all variables, then it is
   discarded. That is, all elements in the resultant list satisfy the predicate \c is_ceq.
*/
list<expr_pair> to_ceqs(ro_environment const & env, optional<ro_metavar_env> const & menv, expr const & e, expr const & H);
/**
   \brief Return true iff \c e is a conditional equation.

   A conditional equation ceq has the form
   <code>
         ceq := (forall x : A, ceq)
             |  lhs = rhs
             |  lhs == rhs
   </code>

   Moreover, for <tt>(forall x : A, ceq)</tt>, the variable x must occur in the \c ceq left-hand-size
   when \c A is not a proposition.
*/
bool is_ceq(ro_environment const & env, optional<ro_metavar_env> const & menv, expr e);
/**
   \brief Return true iff the lhs is identical to the rhs modulo a
   permutation of the conditional equation arguments.
*/
bool is_permutation_ceq(expr e);
void open_ceq(lua_State * L);
}
