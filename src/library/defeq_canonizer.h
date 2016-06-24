/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
/* \brief Return an expression that is definitionally equal to \c e.

   \remark The predicate locals_subset(r, e) holds for the resulting expression r.

   \remark The procedure maintains thread local storage. The results are reset
   whenever ctx.env() is not pointer equal to the environment in the previous call.

   \remark updated is set to true if previous results may have been updated.

   \remark This procedure is meant to be used to canonize type class instances and
   proofs. It is too expensive for arbitrary terms.

   \remark Suppose we invoke defeq_canonize for every type class instance
   in a big term T, and we replace them with the result returned by defeq_canonize.
   If updated is not true, then forall instances I1 and I2 in the resulting term T',
   if I1 and I2 are definitionally equal and have the same local constants, then
   I1 and I2 are structurally equal.

   \remark Suppose we invoke defeq_canonize for every type class instance in a big term T,
   and updated is true in the end. Then, if we reset updated to false and restart the process,
   then eventually updated will be false after a finite number of restarts. */
expr defeq_canonize(type_context & ctx, expr const & e, bool & updated);
}
