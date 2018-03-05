/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/locals.h"
#include "library/private.h"
#include "library/aliases.h"
#include "library/trace.h"
#include "library/aux_definition.h"
#include "library/module.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/compiler/vm_compiler.h"
#include "library/vm/vm.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/unbounded_rec.h"
#include "frontends/lean/elaborator.h"

namespace lean {
static expr replace_rec_apps(type_context_old & ctx, expr const & e) {
    equations_header const & header = get_equations_header(e);
    list<name> actual_names = header.m_fn_actual_names;
    unpack_eqns ues(ctx, e);
    buffer<expr> fns;
    buffer<expr> macro_fns;
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        expr const & fn = ues.get_fn(fidx);
        fns.push_back(fn);
        macro_fns.push_back(mk_rec_fn_macro(head(actual_names), ctx.infer(fn)));
        actual_names = tail(actual_names);
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

static void split_rec_fns(type_context_old & ctx, expr const & e, buffer<expr> & result) {
    equations_header const & header = get_equations_header(e);
    unpack_eqns ues(ctx, e);
    list<name> fn_names        = header.m_fn_names;
    list<name> fn_actual_names = header.m_fn_actual_names;
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        equations_header new_header = header;
        new_header.m_num_fns         = 1;
        new_header.m_fn_names        = to_list(head(fn_names));
        new_header.m_fn_actual_names = to_list(head(fn_actual_names));
        fn_names                     = tail(fn_names);
        fn_actual_names              = tail(fn_actual_names);
        buffer<expr> eqns;
        for (expr const & eqn : ues.get_eqns_of(fidx)) {
            eqns.push_back(ctx.mk_lambda(ues.get_fn(fidx), eqn));
        }
        result.push_back(mk_equations(new_header, eqns.size(), eqns.data()));
    }
}

static expr fix_rec_apps(expr const & e, name_map<expr> const & name2new_type,
                         buffer<expr> const & closure_params) {
    return replace(e, [&](expr const & t) {
            if (is_rec_fn_macro(t)) {
                if (auto new_type = name2new_type.find(get_rec_fn_name(t))) {
                    return some_expr(mk_app(mk_rec_fn_macro(get_rec_fn_name(t), *new_type),
                                            closure_params));
                } else {
                    throw exception("internal error, ill-formed mutual recursive definition");
                }
            } else {
                return none_expr();
            }
        });
}

eqn_compiler_result unbounded_rec(environment & env, elaborator & elab,
                                  metavar_context & mctx, local_context const & lctx,
                                  expr const & e) {
    type_context_old ctx(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);

    /* Replace recursive application with macro, and split mutual definition in n definitions. */
    expr e1 = replace_rec_apps(ctx, e);
    buffer<expr> es;
    split_rec_fns(ctx, e1, es);

    if (is_recursive_eqns(ctx, e)) {
        /* We create auxiliary definitions when compiling mutually recursive equations. */
        buffer<expr> fns;
        buffer<expr> fn_types;
        buffer<expr> counter_examples;
        closure_helper helper(ctx);

        /* 1. Compile pattern matching */

        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            unpack_eqns ues(ctx, es[fidx]);
            auto R = elim_match(env, elab, mctx, lctx, es[fidx]);
            fns.push_back(helper.collect(R.m_fn));
            fn_types.push_back(helper.collect(ctx.infer(ues.get_fn(0))));
            for (list<expr> const & ts : R.m_counter_examples) {
                counter_examples.push_back(mk_app(ues.get_fn(0), ts));
            }
        }

        helper.finalize_collection();

        buffer<level> closure_lvl_params;
        buffer<expr>  closure_params;
        helper.get_level_closure(closure_lvl_params);
        helper.get_expr_closure(closure_params);

        list<name> lvl_names;
        lvl_names = helper.get_norm_level_names();

        equations_header const & header = get_equations_header(e);
        list<name> fn_names             = header.m_fn_names;
        list<name> fn_actual_names      = header.m_fn_actual_names;
        bool zeta                       = get_eqn_compiler_zeta(elab.get_options());

        /* 2. Update fn_types.
           zeta-expand (if needed) and apply closures. */

        name_map<expr> name2type;
        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            name fn_name = head(fn_actual_names);
            expr fn_type = fn_types[fidx];
            if (zeta) {
                fn_type = zeta_expand(lctx, fn_type);
            }
            fn_type   = helper.mk_pi_closure(fn_type);
            fn_types[fidx] = fn_type;
            name2type.insert(fn_name, fn_type);
            fn_actual_names   = tail(fn_actual_names);
        }

        /* 3. Fix recursive applications, declare definition, and private/alias info */

        fn_actual_names      = header.m_fn_actual_names;
        buffer<expr> result_fns;
        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            name fn_name = head(fn_actual_names);
            expr fn_type = fn_types[fidx];
            expr fn      = fns[fidx];
            if (zeta) {
                fn      = zeta_expand(lctx, fn);
            }
            fn = fix_rec_apps(fn, name2type, helper.get_norm_closure_params());
            fn = helper.mk_lambda_closure(fn);

            bool use_self_opt = true;
            bool trusted      = false;
            declaration d     = mk_definition(env, fn_name, lvl_names, fn_type, fn, use_self_opt, trusted);
            env               = module::add(env, check(env, d, true));

            expr result_fn    = mk_app(mk_constant(fn_name, to_list(closure_lvl_params)), closure_params);

            result_fns.push_back(result_fn);

            if (header.m_is_private) {
                env = register_private_name(env, head(fn_names), fn_name);
                env = add_expr_alias(env, head(fn_names), fn_name);
            }

            fn_names          = tail(fn_names);
            fn_actual_names   = tail(fn_actual_names);
        }

        /* 4. Compile. Remark: we need a separate pass because we need to reserve the functions
           and their arities in the VM. */

        buffer<declaration> new_decls;
        for (name const & n : header.m_fn_actual_names) {
            new_decls.push_back(env.get(n));
        }
        try {
            env = vm_compile(env, new_decls);
        } catch (exception & ex) {
            sstream ss;
            ss << "equation compiler failed to generate bytecode for";
            for (name const & n : header.m_fn_names)
                ss << " '" << n << "'";
            throw nested_exception(ss, ex);
        }
        return { to_list(result_fns), to_list(counter_examples) };
    } else {
        lean_assert(!is_recursive_eqns(ctx, e));
        /* If the equations are recursive, we simply compile each one of them and combine the
           results.

           This is NOT an optimization. An auxiliary definition would complicate the use of
           attributes such as [reducible]. For example, consider the following definition.

           @[reducible] meta def tactic := interaction_monad tactic_state

           If we create the auxiliary declaration tactic._main, it will also have to be marked
           as [reducible]. Otherwise the attribute [reducible] at tactic would not have the desired effect.
           In the current system we do not have a mechanism for propagating attributes to auxiliary
           definitions, nor it is clear how the propagation should behave in general (i.e.,
           should we simply propagate it to ALL auxiliary definitions?).
        */
        buffer<expr> fns;
        buffer<expr> counter_examples;

        /* Compile pattern matching */

        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            unpack_eqns ues(ctx, es[fidx]);
            auto R = elim_match(env, elab, mctx, lctx, es[fidx]);
            fns.push_back(R.m_fn);
            for (list<expr> const & ts : R.m_counter_examples) {
                counter_examples.push_back(mk_app(ues.get_fn(0), ts));
            }
        }
        return { to_list(fns), to_list(counter_examples) };
    }
}
}
