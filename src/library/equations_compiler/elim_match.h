/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
struct elim_match_result {
    expr       m_fn;
    list<expr> m_lemmas;
    elim_match_result(expr const & fn, list<expr> const & lemmas):m_fn(fn), m_lemmas(lemmas) {}
};
elim_match_result elim_match(environment & env, options const & opts, metavar_context & mctx, local_context const & lctx, expr const & eqns);
expr mk_nonrec(environment & env, options const & opts, metavar_context & mctx,
               local_context const & lctx, expr const & eqns);
void initialize_elim_match();
void finalize_elim_match();
}
