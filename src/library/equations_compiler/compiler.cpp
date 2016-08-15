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

namespace lean {
#define trace_compiler(Code) lean_trace("eqn_compiler", scope_trace_env _scope1(ctx->env(), ctx); Code)

expr compile_equations(environment const & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                       expr const & eqns) {
    aux_type_context ctx(env, opts, mctx, lctx, transparency_mode::Semireducible);
    trace_compiler(tout() << "compiling\n" << eqns << "\n";);
    trace_compiler(tout() << "recursive: " << is_recursive_eqns(ctx, eqns) << "\n";);

    // expr eqns1 = pack_domain(ctx.get(), eqns);
    // tout() << eqns1 << "\n";
    unsigned arg_idx;
    optional<expr> eqns1 = try_structural_rec(ctx.get(), eqns, arg_idx);
    lean_unreachable();
}

void initialize_compiler() {
    register_trace_class("eqn_compiler");
}
void finalize_compiler() {
}
}
