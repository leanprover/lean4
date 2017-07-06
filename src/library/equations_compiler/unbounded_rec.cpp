/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/locals.h"
#include "library/trace.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/unbounded_rec.h"
namespace lean {
static expr replace_rec_apps(type_context & ctx, expr const & e) {
    unpack_eqns ues(ctx, e);
    buffer<expr> fns;
    buffer<expr> macro_fns;
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        expr const & fn = ues.get_fn(fidx);
        fns.push_back(fn);
        macro_fns.push_back(mk_rec_fn_macro(local_pp_name(fn), ctx.infer(fn)));
    }
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        buffer<expr> & eqns = ues.get_eqns_of(fidx);
        for (expr & eqn : eqns) {
            unpack_eqn ue(ctx, eqn);
            expr new_rhs = replace_locals(ue.rhs(), fns, macro_fns);
            ue.rhs() = new_rhs;
            eqn = ue.repack();
        }
    }
    expr r = ues.repack();
    lean_trace("eqn_compiler", tout() << "using unbounded recursion (meta-definition):\n" << r << "\n";);
    return r;
}

eqn_compiler_result unbounded_rec(environment & env, options const & opts,
                   metavar_context & mctx, local_context const & lctx,
                   expr const & e) {
    type_context ctx(env, opts, mctx, lctx, transparency_mode::Semireducible);
    expr e1 = replace_rec_apps(ctx, e);
    auto R = elim_match(env, opts, mctx, lctx, e1);

    list<expr> counter_examples;
    if (R.m_counter_examples) {
        unpack_eqns ues(ctx, e);
        counter_examples = map2<expr>(R.m_counter_examples, [&] (list<expr> const & es) {
            return mk_app(ues.get_fn(0), es);
        });
    }

    return { {R.m_fn}, counter_examples };
}
}
