/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/state.h"

namespace lean {
namespace blast {
/*
   This module provides a thin layer for creating proof terms at proof-step resolve.
   The idea is to allow us to refactor the code in the future, and implement
   more efficient ways of representing proof terms.

   One current performance bottleneck is unfold_hypotheses_ge.
*/

/** \brief This is currently a noop. */
expr to_proof_expr(expr const & e);

/** \brief Unfold hrefs occurring in \c pr that have a value and were created
    at proof depth >= d */
expr unfold_hypotheses_ge(state const & s, expr const & pr, unsigned d);
inline expr unfold_hypotheses_ge(state const & s, expr const & pr) {
    return unfold_hypotheses_ge(s, pr, s.get_proof_depth());
}

/** \brief Create an lambda abstraction. */
expr mk_proof_lambda(state const & s, list<expr> const & hs, expr const & pr);

/** \brief Create an application using the app_builder */
expr mk_proof_app(name const & fname, unsigned nargs, expr const * args);
expr mk_proof_app(expr const & f, unsigned nargs, expr const * args);
}}
