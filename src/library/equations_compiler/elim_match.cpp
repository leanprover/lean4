/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

namespace lean {
#define trace_match(Code) lean_trace(name({"eqn_compiler", "elim_match"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)

struct elim_match_fn {
    type_context & m_ctx;
    elim_match_fn(type_context & ctx):m_ctx(ctx) {}

    struct equation {
        list<expr> m_vars;
        list<expr> m_patterns;
        expr       m_rhs;
    };

    struct program {
        /* Variables that still need to be matched/processed */
        list<expr> m_var_stack;
        list<expr> m_equations;
    };


    pair<expr, environment> operator()(expr const & e) {
        unpack_eqns ues(m_ctx, e);
        lean_assert(ues.get_num_fns() == 1);

        lean_unreachable();
    }
};

pair<expr, environment> elim_match(type_context & ctx, expr const & eqns) {
    return elim_match_fn(ctx)(eqns);
}

void initialize_elim_match() {
    register_trace_class({"eqn_compiler", "elim_match"});
}
void finalize_elim_match() {
}
}
