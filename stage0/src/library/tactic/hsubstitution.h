/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_map.h"
#include "kernel/expr.h"

namespace lean {
/* Some tactics substitute hypotheses with new ones and/or terms.
   We track these substitutions using hsubstitution datastructure.
   It is just a mapping from the hypothesis original (internal) name
   to an expression. The new expression should be well-formed with
   respect to the new goal. */
typedef name_map<expr> hsubstitution;

/* \brief Given `e`, for each (x := v) in `s` replace `x` with `v` in `e` */
expr apply(expr const & e, hsubstitution const & s);
/* \brief (map es apply) */
list<expr> apply(list<expr> const & es, hsubstitution const & s);
/* \brief Return a new hsubstitution containing (x := apply(v, s2)) for
   each (x := v) in `s1`. */
hsubstitution apply(hsubstitution const & s1, hsubstitution const & s2);

/* \brief Return a new hsubstitution containing the entries of `s1` and `s2`.
   \remark the entries in `s2` have precedence over the ones in `s1`. */
hsubstitution merge(hsubstitution const & s1, hsubstitution const & s2);
}
