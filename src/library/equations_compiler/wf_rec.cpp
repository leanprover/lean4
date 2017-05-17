/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/type_context.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/app_builder.h"
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

    expr             m_R;
    expr             m_R_wf;

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

    expr_pair mk_wf_relation(expr const & eqns) {
        lean_assert(get_equations_header(eqns).m_num_fns == 1);
        type_context ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        try {
            expr fn_type = ctx.relaxed_whnf(ctx.infer(ues.get_fn(0)));
            lean_assert(is_pi(fn_type));
            expr d       = binding_domain(fn_type);
            expr wf      = mk_app(ctx, get_has_well_founded_name(), d);
            if (auto inst = ctx.mk_class_instance(wf)) {
                bool mask[2] = {true, true};
                expr args[2] = {d, *inst};
                expr r   = mk_app(ctx, get_has_well_founded_r_name(), 2, mask, args);
                expr wf  = mk_app(ctx, get_has_well_founded_wf_name(), 2, mask, args);
                return expr_pair(r, wf);
            }
        } catch (exception & ex) {
            throw nested_exception(some_expr(m_ref),
                                   "failed to create well founded relation using type class resolution",
                                   ex);
        }
        throw generic_exception(m_ref, "failed to create well founded relation using type class resolution");
    }

    expr operator()(expr eqns) {
        m_ref    = eqns;
        m_header = get_equations_header(eqns);
        /* Make sure all functions are unary */
        eqns     = pack_domain(eqns);
        trace_debug_wf(tout() << "after pack_domain\n" << eqns << "\n";);

        equations_header const & header = get_equations_header(eqns);
        if (header.m_num_fns > 1) {
            // TODO(Leo): combine functions
            throw exception("support for mutual recursion has not been implemented yet");
        }

        if (is_wf_equations(eqns)) {
            m_R    = equations_wf_rel(eqns);
            m_R_wf = equations_wf_proof(eqns);
        } else {
            std::tie(m_R, m_R_wf) = mk_wf_relation(eqns);
        }

        {
            lean_trace_init_bool(name({"eqn_compiler", "wf_rec"}), get_pp_implicit_name(), true);
            trace_wf(tout() << "using well_founded relation\n" << m_R << "\n";);
        }

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
