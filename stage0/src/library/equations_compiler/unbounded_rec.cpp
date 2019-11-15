/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/locals.h"
#include "library/private.h"
#include "library/util.h"
#include "library/aliases.h"
#include "library/trace.h"
#include "library/aux_definition.h"
#include "library/compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/unbounded_rec.h"
#include "frontends/lean/elaborator.h"

namespace lean {

static local_context split_rec_fns(environment const & env, metavar_context & mctx, local_context const & lctx, expr const & e, buffer<expr> & aux_rec_fns, buffer<expr> & result) {
    equations_header const & header = get_equations_header(e);
    type_context_old ctx1(env, options(), mctx, lctx, transparency_mode::Semireducible); // TODO(Leo): fix options
    unpack_eqns ues1(ctx1, e);
    /* Create declarations for recursive functions at `new_lctx` */
    local_context new_lctx = lctx;
    for (unsigned fidx = 0; fidx < ues1.get_num_fns(); fidx++) {
        expr const & fn = ues1.get_fn(fidx);
        local_decl decl = ctx1.lctx().get_local_decl(fn);
        expr aux_rec_fn = new_lctx.mk_local_decl(name(decl.get_user_name(), "_rec"), ctx1.infer(fn), decl.get_info());
        aux_rec_fns.push_back(aux_rec_fn);
    }

    /* Split equations, and replace recursive calls with aux_rec_fns */
    type_context_old ctx2(env, options(), ctx1.mctx(), new_lctx, transparency_mode::Semireducible); // TODO(Leo): fix options
    unpack_eqns ues2(ctx2, e);
    names fn_names        = header.m_fn_names;
    names fn_actual_names = header.m_fn_actual_names;
    buffer<expr> fns;
    for (unsigned fidx = 0; fidx < ues2.get_num_fns(); fidx++) {
        expr const & fn = ues2.get_fn(fidx);
        fns.push_back(fn);
    }
    for (unsigned fidx = 0; fidx < ues2.get_num_fns(); fidx++) {
        equations_header new_header = header;
        new_header.m_num_fns         = 1;
        new_header.m_fn_names        = names(head(fn_names));
        new_header.m_fn_actual_names = names(head(fn_actual_names));
        fn_names                     = tail(fn_names);
        fn_actual_names              = tail(fn_actual_names);
        buffer<expr> eqns;
        for (expr const & eqn : ues2.get_eqns_of(fidx)) {
            unpack_eqn ue(ctx2, eqn);
            expr new_rhs = replace_locals(ue.rhs(), fns, aux_rec_fns);
            ue.rhs() = new_rhs;
            eqns.push_back(ctx2.mk_lambda(ues2.get_fn(fidx), ue.repack()));
        }
        result.push_back(mk_equations(new_header, eqns.size(), eqns.data()));
    }

    mctx = ctx2.mctx();
    return new_lctx;
}

static expr fix_rec_apps(expr const & e, name_map<name> const & aux_rec_name2actual_name,
                         levels const & closure_levels, buffer<expr> const & closure_params) {
    return replace(e, [&](expr const & t) {
            if (is_fvar(t)) {
                if (name const * actual_name = aux_rec_name2actual_name.find(fvar_name(t))) {
                    return some_expr(mk_app(mk_constant(*actual_name, closure_levels), closure_params));
                } else {
                    return none_expr();
                }
            } else {
                return none_expr();
            }
        });
}

eqn_compiler_result unbounded_rec(environment & env, elaborator & elab,
                                  metavar_context & mctx, local_context const & lctx,
                                  expr const & e, optional<expr> const & safe_result) {
    lean_assert(!safe_result || is_equations_result(*safe_result));
    /* Split recursive equations by using new auxiliary `.rec` locals */
    buffer<expr> aux_rec_fns;
    buffer<expr> es;
    local_context aux_lctx = split_rec_fns(env, mctx, lctx, e, aux_rec_fns, es);
    type_context_old ctx(env, mctx, aux_lctx, elab.get_cache(), transparency_mode::Semireducible);

    /* Create set of auxiliary locals and mapping from auxiliary local to actual name */
    equations_header const & header = get_equations_header(e);
    name_set       aux_rec_fn_names;
    name_map<name> aux_rec_fn_name2actual_name;
    names fn_actual_names = header.m_fn_actual_names;
    for (expr const & aux_rec_fn : aux_rec_fns) {
        aux_rec_fn_names.insert(fvar_name(aux_rec_fn));
        aux_rec_fn_name2actual_name.insert(fvar_name(aux_rec_fn), head(fn_actual_names));
        fn_actual_names = tail(fn_actual_names);
    }

    if (is_recursive_eqns(ctx, e)) {
        /* We create auxiliary definitions when compiling mutually recursive equations. */
        buffer<expr> fns;
        buffer<expr> fn_types;
        buffer<expr> counter_examples;
        closure_helper helper(ctx);

        /* 1. Compile pattern matching */
        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            unpack_eqns ues(ctx, es[fidx]);
            auto R = elim_match(env, elab, mctx, aux_lctx, es[fidx]);

            /* We must not collect auxiliary locals in `aux_rec_fns` */
            fns.push_back(helper.collect(R.m_fn, aux_rec_fn_names));
            fn_types.push_back(helper.collect(ctx.infer(ues.get_fn(0))));
            for (list<expr> const & ts : R.m_counter_examples) {
                counter_examples.push_back(mk_app(ues.get_fn(0), ts));
            }
            if (safe_result) {
                lean_assert(is_equations_result(*safe_result));
                lean_assert(get_equations_result_size(*safe_result) == es.size());
                helper.collect(get_equations_result(*safe_result, fidx));
            }
        }
        helper.finalize_collection();

        buffer<level> closure_lvl_args;
        buffer<expr>  closure_args;
        helper.get_level_closure(closure_lvl_args);
        helper.get_expr_closure(closure_args);

        names lvl_names;
        lvl_names = helper.get_norm_level_names();
        levels lvls = lparams_to_levels(lvl_names);
        buffer<expr> const & params = helper.get_norm_closure_params();

        bool zeta = get_eqn_compiler_zeta(elab.get_options());

        /* 2. Update fn_types.
           zeta-expand (if needed) and apply closures. */
        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            expr fn_type = fn_types[fidx];
            if (zeta) {
                fn_type = zeta_expand(aux_lctx, fn_type);
            }
            fn_type   = helper.mk_pi_closure(fn_type);
            fn_types[fidx]  = fn_type;
        }

        /* 3. Fix recursive applications, and create definitions */
        buffer<definition_val> new_defs;
        fn_actual_names      = header.m_fn_actual_names;
        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            name fn_name = head(fn_actual_names);
            expr fn_type = fn_types[fidx];
            expr fn      = fns[fidx];
            if (zeta) {
                fn      = zeta_expand(aux_lctx, fn);
            }
            fn = fix_rec_apps(fn, aux_rec_fn_name2actual_name, lvls, params);
            fn = helper.mk_lambda_closure(fn);

            bool is_meta      = true;
            if (optional<name> safe_fn_name = is_unsafe_rec_name(fn_name)) {
                constant_info safe_fn_info = env.get(*safe_fn_name);
                if (!ctx.is_def_eq(safe_fn_info.get_type(), fn_type)) {
                    throw generic_exception(e, sstream() << "equation compiler failed to generate auxiliary declaration '" << fn_name << "' for the compiler with matching type");
                }
            }
            new_defs.push_back(mk_definition_val(env, fn_name, lvl_names, fn_type, fn, is_meta));
            fn_actual_names   = tail(fn_actual_names);
        }

        env = env.add(mk_mutual_definitions(definition_vals(new_defs)));

        /* 4. Create result and add private/alias info */
        buffer<expr> result_fns;
        names fn_names       = header.m_fn_names;
        fn_actual_names      = header.m_fn_actual_names;
        for (unsigned fidx = 0; fidx < es.size(); fidx++) {
            name fn_name = head(fn_actual_names);
            expr result_fn    = mk_app(mk_constant(fn_name, levels(closure_lvl_args)), closure_args);

            result_fns.push_back(result_fn);
            if (header.m_is_private) {
                env = add_expr_alias(env, head(fn_names), fn_name);
            }
            fn_names        = tail(fn_names);
            fn_actual_names = tail(fn_actual_names);
        }

        /* 5. Compile. Remark: we need a separate pass because we need to reserve the functions
           and their arities in the VM. */
        if (header.m_gen_code) {
            try {
                env = compile(env, elab.get_options(), header.m_fn_actual_names);
            } catch (exception & ex) {
                sstream ss;
                ss << "equation compiler failed to generate bytecode for";
                for (name const & n : header.m_fn_names)
                    ss << " '" << n << "'";
            throw nested_exception(ss, std::current_exception());
            }
        }
        return { to_list(result_fns), to_list(counter_examples) };
    } else  {
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
