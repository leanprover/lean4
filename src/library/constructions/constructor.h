/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/type_context.h"
namespace lean {
/* If e1 and e2 are constructor applications, the constructors are different, and (h : e1 = e2), then
   return a proof for false. */
optional<expr> mk_constructor_eq_constructor_inconsistency_proof(type_context_old & ctx, expr const & e1, expr const & e2, expr const & h);

/* If e1 and e2 are constructor applications, the constructors are different, then
   return a proof for not (e1 = e2). */
optional<expr> mk_constructor_ne_constructor_proof(type_context_old & ctx, expr const & e1, expr const & e2);

/* If e1 and e2 are constructor applications for the same constructor, and (h : e1 = e2), then
   return true, and store the triples (a_i, b_i, hab_i) at result, where (hab_i : a_i = b_i)
   and a_i (b_i) are constructor fields of e1 (e2). */
bool mk_constructor_eq_constructor_implied_eqs(type_context_old & ctx, expr const & e1, expr const & e2, expr const & h,
                                               buffer<std::tuple<expr, expr, expr>> & result);
}
