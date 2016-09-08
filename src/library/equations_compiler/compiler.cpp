/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/pack_domain.h"
#include "library/equations_compiler/structural_rec.h"
#include "library/equations_compiler/unbounded_rec.h"
#include "library/equations_compiler/elim_match.h"

namespace lean {
#define trace_compiler(Code) lean_trace("eqn_compiler", scope_trace_env _scope1(ctx.env(), ctx); Code)

expr compile_equations(environment & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                       expr const & eqns) {
    type_context ctx(env, opts, mctx, lctx, transparency_mode::Semireducible);
    trace_compiler(tout() << "compiling\n" << eqns << "\n";);
    trace_compiler(tout() << "recursive: " << is_recursive_eqns(ctx, eqns) << "\n";);
    if (equations_num_fns(eqns) == 1) {
        if (!is_recursive_eqns(ctx, eqns)) {
            return mk_nonrec(env, opts, mctx, lctx, eqns);
        } else if (optional<expr> r = try_structural_rec(env, opts, mctx, lctx, eqns)) {
            return *r;
        }
    }

    // test pack_domain
    pack_domain(ctx, eqns);

    // test unbounded_rec
    // unbounded_rec(ctx.get(), eqns);


    lean_unreachable();
}

void initialize_compiler() {
    register_trace_class("eqn_compiler");
    register_trace_class(name{"debug", "eqn_compiler"});
}
void finalize_compiler() {
}
}
