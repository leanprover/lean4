/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/structural_rec.h"
#include "library/equations_compiler/unbounded_rec.h"
#include "library/equations_compiler/wf_rec.h"
#include "library/equations_compiler/partial_rec.h"
#include "library/equations_compiler/elim_match.h"
#include "frontends/lean/elaborator.h"

namespace lean {
#define trace_compiler(Code) lean_trace("eqn_compiler", scope_trace_env _scope1(ctx.env(), ctx); Code)

static bool has_nested_rec(local_context const & lctx, expr const & eqns) {
    return static_cast<bool>(find(eqns, [&](expr const & e, unsigned) {
                                            return is_fvar(e) && is_rec(lctx.get_local_decl(e).get_info());
                                        }));
}

static eqn_compiler_result compile_equations_core(environment & env, elaborator & elab, metavar_context & mctx, local_context const & lctx, expr const & eqns) {
    type_context_old ctx(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
    trace_compiler(tout() << "compiling\n" << eqns << "\n";);
    trace_compiler(tout() << "recursive:          " << is_recursive_eqns(ctx, eqns) << "\n";);
    trace_compiler(tout() << "nested recursion:   " << has_nested_rec(lctx, eqns) << "\n";);
    trace_compiler(tout() << "using_well_founded: " << is_wf_equations(eqns) << "\n";);
    equations_header const & header = get_equations_header(eqns);
    trace_compiler(tout() << "partial:            " << header.m_is_partial << "\n";);
    // lean_assert(header.m_is_unsafe || !has_nested_rec(eqns));

    if (header.m_is_unsafe) {
        if (is_wf_equations(eqns)) {
            throw exception("invalid use of 'using_well_founded', we do not need to use well founded recursion for unsafe definitions, since they can use unbounded recursion");
        }
        return unbounded_rec(env, elab, mctx, lctx, eqns);
    }

    if (header.m_is_partial && is_recursive_eqns(ctx, eqns)) {
        if (is_wf_equations(eqns)) {
            throw exception("invalid use of 'using_well_founded', we do not need to use well founded recursion for partial definitions, since they can use unbounded recursion");
        }
        return partial_rec(env, elab, mctx, lctx, eqns);
    }

    if (is_wf_equations(eqns)) {
        return wf_rec(env, elab, mctx, lctx, eqns);
    }

    if (header.m_num_fns == 1) {
        if (!is_recursive_eqns(ctx, eqns)) {
            return mk_nonrec(env, elab, mctx, lctx, eqns);
        } else if (auto r = try_structural_rec(env, elab, mctx, lctx, eqns)) {
            return *r;
        }
    }

    return wf_rec(env, elab, mctx, lctx, eqns);
}

static expr remove_aux_main_name(expr const & e) {
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    if (!is_constant(fn)) return e;
    name n = const_name(fn);
    if (n.is_string() && n.get_string() == "_main") {
        n = n.get_prefix();
        fn = mk_constant(n, const_levels(fn));
        return mk_app(fn, args);
    }
    return e;
}

struct eta_expand_rec_apps_fn : public replace_visitor_with_tc {
    eta_expand_rec_apps_fn(type_context_old & ctx): replace_visitor_with_tc(ctx) {}

    virtual expr visit_fvar(expr const & e) {
        if (is_rec(m_ctx.lctx().get_local_decl(e).get_info())) {
            expr e2 = m_ctx.eta_expand(e);
            lean_assert(!is_fvar(e2));
            return visit(e2);
        }
        return e;
    }

    virtual expr visit_app(expr const & e) {
        expr const & fn = app_fn(e);
        if (is_fvar(fn) && is_rec(m_ctx.lctx().get_local_decl(fn).get_info())) {
            // do not eta-expand `fn`
            expr arg = visit(app_arg(e));
            return mk_app(fn, arg);
        } else {
            return replace_visitor::visit_app(e);
        }
    }
};

static expr compile_equations_main(environment & env, elaborator & elab,
                                   metavar_context & mctx, local_context const & lctx, expr const & _eqns,
                                   bool report_cexs) {
    // all following code assumes that all recursive occurrences are applications
    type_context_old ctx(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
    expr eqns = eta_expand_rec_apps_fn(ctx)(_eqns);
    // tout() << "compile_equations_main\n" << eqns << "\n";
    // equations_header const & header = get_equations_header(eqns);
    eqn_compiler_result r;
    // if (!header.m_is_unsafe && has_nested_rec(eqns)) {
    //    r = pull_nested_rec_fn(env, elab, mctx, lctx)(eqns);
    //     tout() << "pull_nested_rec_fn\n" << head(r.m_fns) << "\n";
    // } else {
    r = compile_equations_core(env, elab, mctx, lctx, eqns);
    // }
    if (report_cexs && r.m_counter_examples) {
        auto pp = mk_pp_ctx(env, elab.get_options(), mctx, lctx);
        auto fmt = format("non-exhaustive match, the following cases are missing:");
        for (auto & ce : r.m_counter_examples) {
            fmt += line() + pp(remove_aux_main_name(ce));
        }
        elab.report_or_throw({_eqns, fmt});
    }

    buffer<expr> fns; to_buffer(r.m_fns, fns);
    expr eqn_result = mk_equations_result(fns.size(), fns.data());
    return eqn_result;
}

expr compile_equations(environment & env, elaborator & elab, metavar_context & mctx, local_context const & lctx, expr const & eqns) {
    equations_header const & header = get_equations_header(eqns);
    type_context_old ctx(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
    if (!header.m_is_unsafe &&
        !header.m_is_lemma &&
        !header.m_is_noncomputable &&
        /* Remark: we don't need special compilation scheme for non recursive equations */
        is_recursive_eqns(ctx, eqns)) {
        /* Compile equations but do not generate code since we will use `brec_on` or `well_founded.fix`. */
        equations_header new_header = header;
        new_header.m_gen_code       = false;
        expr result = compile_equations_main(env, elab, mctx, lctx, update_equations(eqns, new_header), true);
        /* Then, we compile the equations again using `unsafe` and generate code.
           The motivations are:
           - Clear execution cost semantics for recursive functions.
           - Auxiliary unsafe definition may assist recursive definition unfolding in the type_context_old object. */
        equations_header aux_header = header;
        aux_header.m_is_unsafe  = true;
        aux_header.m_is_partial = false;
        aux_header.m_aux_lemmas = false;
        aux_header.m_fn_actual_names = map(header.m_fn_actual_names, mk_unsafe_rec_name);
        expr aux_eqns = remove_wf_annotation_from_equations(update_equations(eqns, aux_header));
        aux_eqns      = eta_expand_rec_apps_fn(ctx)(aux_eqns);
        unbounded_rec(env, elab, mctx, lctx, aux_eqns, some_expr(result));
        return result;
    } else {
        return compile_equations_main(env, elab, mctx, lctx, eqns, true);
    }
}

void initialize_eqn_compiler() {
}

void finalize_eqn_compiler() {
}
}
