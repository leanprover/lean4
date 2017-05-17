/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/type_context.h"
#include "library/trace.h"
#include "library/equations_compiler/pack_domain.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/util.h"

namespace lean {
#define trace_wf(Code) lean_trace(name({"eqn_compiler", "wf_rec"}), type_context ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)

#define trace_debug_wf(Code) lean_trace(name({"debug", "eqn_compiler", "wf_rec"}), type_context ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)

struct wf_rec_fn {
    environment      m_env;
    options          m_opts;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;

    wf_rec_fn(environment const & env, options const & opts,
              metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_opts(opts), m_mctx(mctx), m_lctx(lctx) {
    }

    type_context mk_type_context(local_context const & lctx) {
        return type_context(m_env, m_opts, m_mctx, lctx, transparency_mode::Semireducible);
    }

    type_context mk_type_context() {
        return mk_type_context(m_lctx);
    }

    expr pack_domain(expr const & eqns) {
        type_context ctx = mk_type_context();
        return ::lean::pack_domain(ctx, eqns);
    }

    expr operator()(expr eqns) {
        m_ref    = eqns;
        m_header = get_equations_header(eqns);
        /* Make sure all functions are unary */
        eqns     = pack_domain(eqns);
        trace_debug_wf(tout() << "after pack_domain\n" << eqns << "\n";);

        // TODO(Leo):
        throw exception("support for well-founded recursion has not been implemented yet, "
                        "use 'set_option trace.eqn_compiler true' for additional information");
    }
};

/** \brief (Try to) eliminate "recursive calls" in the equations \c eqns by using well founded recursion.
    If successful, elim_match is used to compile pattern matching. */
expr wf_rec(environment & env, options const & opts,
            metavar_context & mctx, local_context const & lctx,
            expr const & eqns) {
    wf_rec_fn proc(env, opts, mctx, lctx);
    expr r = proc(eqns);
    env    = proc.m_env;
    mctx   = proc.m_mctx;
    return r;
}

void initialize_wf_rec() {
    register_trace_class({"eqn_compiler", "wf_rec"});
    register_trace_class({"debug", "eqn_compiler", "wf_rec"});
}

void finalize_wf_rec() {
}
}
