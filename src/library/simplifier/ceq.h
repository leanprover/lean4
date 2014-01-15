/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/environment.h"
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

   P                    --->   P = true   (if none of the rules above apply and P is not an equality)
*/
list<expr_pair> to_ceqs(ro_environment const & env, expr const & e, expr const & H);
void open_ceq(lua_State * L);
}


