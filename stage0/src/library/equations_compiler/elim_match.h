/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/equations_compiler/util.h"
namespace lean {
class elaborator;
struct elim_match_result {
    expr       m_fn;
    list<expr> m_lemmas;
    list<list<expr>> m_counter_examples;
};
elim_match_result elim_match(environment & env, elaborator & elab, metavar_context & mctx,
                             local_context const & lctx, expr const & eqns);
eqn_compiler_result mk_nonrec(environment & env, elaborator & elab, metavar_context & mctx,
                              local_context const & lctx, expr const & eqns);
void initialize_elim_match();
void finalize_elim_match();
}
