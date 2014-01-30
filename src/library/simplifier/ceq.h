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
/*
  Given a ceq C, in principle, whenever we want to create an application (C t1 ... tn),
  we must check whether the types of t1 ... tn are convertible to the expected types by C.

  This check is needed because of universe cumulativity.
  Here is an example that illustrates the issue:

    universe U >= 2
    variable f (A : (Type 1)) : (Type 1)
    axiom Ax1 (a : Type) : f a = a
    rewrite_set S
    add_rewrite Ax1 eq_id : S
    theorem T1 (A : (Type 1)) : f A = A
    := by simp S

  In this example, Ax1 is a ceq. It has an argument of type Type.
  Note that f expects an element of type (Type 1). So, the term (f a) is type correct.

  The axiom Ax1 is only for arguments convertible to Type (i.e., Type 0), but
  argument A in T1 lives in (Type 1)

  Scenarios like the one above do not occur very frequently. Moveover, it is quite expensive
  to check if the types are convertible for each application of a ceq.

  In most cases, we can statically determine that the checks are not needed when applying
  a ceq. Here is a sufficient condition for skipping the test: if for all
  arguments x of ceq, one of the following conditions must hold:
     1- The argument has type (Type U). In Lean, (Type U) is the maximal universe.
     2- The argument is a proposition.
     3- There is an application (f x) in the left-hand-side, and
        the type expected by f is definitionally equal to the argument type.
     4- There is an application (f (x ...)) in the left-hand-side,  and
        the type expected by f is definitionally equal to the type of (x ...)
     5- There is an application (f (fun y, x)) in the left-hand-side,
        and the type expected by f is definitionally equal to the type of (fun y, x)
  \pre is_ceq(env, menv, ceq)
*/
bool is_safe_to_skip_check_ceq_types(ro_environment const & env, optional<ro_metavar_env> const & menv, expr ceq);

void open_ceq(lua_State * L);
}
