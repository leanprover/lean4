/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"
#include "library/tactic/location.h"

namespace lean {
expr mk_rewrite_unfold(list<name> const & ns, bool force_unfold, location const & loc);
expr mk_rewrite_reduce(location const & loc);
expr mk_rewrite_reduce_to(expr const & e, location const & loc);
expr mk_rewrite_fold(expr const & e, location const & loc);
expr mk_rewrite_once(optional<expr> const & pattern, expr const & H, bool symm, location const & loc);
expr mk_rewrite_zero_or_more(optional<expr> const & pattern, expr const & H, bool symm, location const & loc);
expr mk_rewrite_one_or_more(optional<expr> const & pattern, expr const & H, bool symm, location const & loc);
expr mk_rewrite_at_most_n(optional<expr> const & pattern, expr const & H, bool symm, unsigned n, location const & loc);
expr mk_rewrite_exactly_n(optional<expr> const & pattern, expr const & H, bool symm, unsigned n, location const & loc);
bool is_rewrite_unfold_step(expr const & e);
bool is_rewrite_step(expr const & e);

/** \brief Create a rewrite tactic expression, where elems was created using \c mk_rewrite_* procedures. */
expr mk_rewrite_tactic_expr(buffer<expr> const & elems);
expr mk_xrewrite_tactic_expr(buffer<expr> const & elems);
expr mk_krewrite_tactic_expr(buffer<expr> const & elems);

void initialize_rewrite_tactic();
void finalize_rewrite_tactic();
}
