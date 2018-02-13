/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
class abstract_context_cache;
/** \brief Erase irrelevant terms (e.g., proofs, types, eq.rec, subtypes, etc).
    The parameters, motive and indices are also erased from cases_on applications.

    \remark The resultant term cannot be type checked. So, any preprocessing step
    that requires type inference cannot be applied after this transformation.

    \remark This procedure also replace occurrences of rec_fn_macro with constants.
    The rec_fn_macro is only used to make sure the result type checks.
    So, since the result will not type check anyway, there is no point in using them. */
expr erase_irrelevant(environment const & env, abstract_context_cache & cache, expr const & e);
/** \brief Neutral auxiliary term. */
bool is_neutral_expr(expr const & e);
bool is_unreachable_expr(expr const & e);

expr mk_neutral_expr();
expr mk_unreachable_expr();

void initialize_erase_irrelevant();
void finalize_erase_irrelevant();
}
