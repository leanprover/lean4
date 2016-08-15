/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/pack_domain.h"

namespace lean {
expr compile_equations(environment const & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                       expr const & eqns) {
    aux_type_context ctx(env, opts, mctx, lctx);
    tout() << eqns << "\n";
    expr eqns1 = pack_domain(ctx.get(), eqns);
    tout() << eqns1 << "\n";
    lean_unreachable();
}
}
