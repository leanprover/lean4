/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/type_context.h"
#include "library/equations_compiler/structural_rec.h"
#include "frontends/lean/elaborator.h"

namespace lean {
struct partial_rec_fn {
    environment      m_env;
    elaborator &     m_elab;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;

    partial_rec_fn(environment const & env, elaborator & elab,
                   metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_elab(elab), m_mctx(mctx), m_lctx(lctx) {
    }

    options const & get_options() const {
        return m_elab.get_options();
    }

    type_context_old mk_type_context(local_context const & lctx) {
        return type_context_old(m_env, m_mctx, lctx, m_elab.get_cache(), transparency_mode::Semireducible);
    }

    type_context_old mk_type_context() {
        return mk_type_context(m_lctx);
    }

    optional<expr> find_arg_with_given_type(type_context_old & ctx, expr const & type) {
        type_context_old::transparency_scope scope(ctx, transparency_mode::Reducible);
        optional<expr> result;
        ctx.lctx().for_each([&](local_decl const & decl) {
                if (!result && ctx.is_def_eq(decl.get_type(), type)) {
                    result = decl.mk_ref();
                }
            });
        return result;
    }

    optional<expr> mk_inhabitant(type_context_old & ctx, expr const & type) {
        level lvl        = get_level(ctx, type);
        expr inhabited_result     = mk_app(mk_constant(get_inhabited_name(), {lvl}), type);
        optional<expr> inhabitant = ctx.mk_class_instance(inhabited_result);
        if (!inhabitant)
            return none_expr();
        return some_expr(mk_app(mk_constant(get_inhabited_default_name(), {lvl}), type, *inhabitant));
    }

    expr mk_base_case_eq(type_context_old & ctx, expr const & fn, unsigned arity, expr const & new_fn) {
        expr fn_type     = ctx.infer(fn);
        expr result_type = fn_type;
        type_context_old::tmp_locals args(ctx);
        for (unsigned i = 0; i < arity; i++) {
            result_type  = ctx.relaxed_whnf(result_type);
            expr arg     = args.push_local_from_binding(result_type);
            result_type  = instantiate(binding_body(result_type), arg);
        }
        expr rhs;
        if (optional<expr> inh = mk_inhabitant(ctx, result_type)) {
            rhs = *inh;
        } else if (optional<expr> arg = find_arg_with_given_type(ctx, result_type)) {
            rhs = *arg;
        } else {
            throw generic_exception(m_ref, "failed to compile partial definition, failed to synthesize result type inhabitant");
        }
        expr zero   = mk_constant(get_nat_zero_name());
        expr lhs    = mk_app(mk_app(new_fn, zero), args.as_buffer());
        expr new_eq = mk_equation(lhs, rhs);
        return ctx.mk_lambda(args.as_buffer(), new_eq);
    }

    void update_eqs(type_context_old & ctx, unpack_eqns & ues, expr const & fn, expr const & new_fn) {
        unsigned arity      = ues.get_arity_of(0);
        buffer<expr> & eqns = ues.get_eqns_of(0);
        buffer<expr> new_eqns;
        /* Add base case */
        new_eqns.push_back(mk_base_case_eq(ctx, fn, arity, new_fn));
        /* Add (succ fuel) pattern to each equation */
        for (expr const & eqn : eqns) {
            type_context_old::tmp_locals locals(ctx);
            unpack_eqn ue(ctx, eqn);
            expr lhs         = ue.lhs();
            expr rhs         = ue.rhs();
            expr fuel        = ue.add_var_front("fuel", mk_nat_type());
            expr succ_fuel   = mk_app(mk_constant(get_nat_succ_name()), fuel);
            buffer<expr> lhs_args;
            get_app_args(lhs, lhs_args);
            expr new_lhs     = mk_app(mk_app(new_fn, succ_fuel), lhs_args);
            expr new_fn_fuel = mk_app(new_fn, fuel);
            expr new_rhs     = replace_local(rhs, fn, new_fn_fuel);
            ue.lhs()         = new_lhs;
            ue.rhs()         = new_rhs;
            new_eqns.push_back(ue.repack());
        }
        eqns = new_eqns;
    }

    expr add_fuel_param(expr const & eqns) {
        type_context_old ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        if (ues.get_num_fns() != 1) {
            throw generic_exception(m_ref, "failed to compile partial definition, mutual recursion is not supported yet");
        }
        expr fn          = ues.get_fn(0);
        expr fn_type     = ctx.infer(fn);
        expr new_fn_type = mk_arrow(mk_nat_type(), fn_type);
        expr new_fn      = ues.update_fn_type(0, new_fn_type);
        update_eqs(ctx, ues, fn, new_fn);
        expr new_eqns    = ues.repack();
        m_mctx           = ctx.mctx();
        /* Add `_fueled` suffix */
        equations_header header       = get_equations_header(new_eqns);
        equations_header new_header   = header;
        new_header.m_fn_names         = names(name(head(header.m_fn_names), "_fueled"));
        new_header.m_fn_actual_names  = names(name(head(header.m_fn_actual_names), "_fueled"));
        return update_equations(new_eqns, new_header);
    }

    list<expr> add_some_fuel(list<expr> const & fns) {
        type_context_old ctx  = mk_type_context();
        names fn_names        = m_header.m_fn_names;
        names fn_actual_names = m_header.m_fn_actual_names;
        expr huge_fuel        = mk_constant(get_huge_fuel_name());
        return map(fns, [&](expr const & fueled_fn) {
                name fn_name        = head(fn_names);
                name fn_actual_name = head(fn_actual_names);
                fn_names            = tail(fn_names);
                fn_actual_names     = tail(fn_actual_names);
                expr fn_val         = mk_app(fueled_fn, huge_fuel);
                expr fn_type        = ctx.infer(fn_val);
                expr r;
                std::tie(m_env, r) = mk_aux_definition(m_env, get_options(), m_mctx, m_lctx, m_header,
                                                       fn_name, fn_actual_name, fn_type, fn_val);
                return r;
            });
    }

    eqn_compiler_result operator()(expr const & eqns) {
        m_ref         = eqns;
        m_header      = get_equations_header(eqns);
        // TODO(Leo): if it mutual recursion, then we need to "pack" functions, and then add auxiliary "fuel" parameter.
        expr new_eqns = add_fuel_param(eqns);
        optional<eqn_compiler_result> R = try_structural_rec(m_env, m_elab, m_mctx, m_lctx, new_eqns);
        if (!R)
            throw generic_exception(m_ref, "failed to compile partial definition, structural recursion failed after adding fuel");
        // TODO(Leo): if it is mutual recursion, then we need to "unpack" result, and then add default "fuel".
        list<expr> fns = add_some_fuel(R->m_fns);
        return eqn_compiler_result({ fns, R->m_counter_examples });
    }
};

eqn_compiler_result partial_rec(environment & env, elaborator & elab,
                                metavar_context & mctx, local_context const & lctx,
                                expr const & eqns) {
    partial_rec_fn proc(env, elab, mctx, lctx);
    auto r = proc(eqns);
    env    = proc.m_env;
    mctx   = proc.m_mctx;
    return r;
}
}
