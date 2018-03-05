/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <iostream>
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/attribute_manager.h"
#include "library/type_context.h"
#include "library/protected.h"
#include "library/local_context.h"
#include "library/app_builder.h"
#include "library/util.h"
#include "library/class.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/constructions/has_sizeof.h"
#include "library/constructions/util.h"

namespace lean {

static name * g_simp_sizeof = nullptr;
static simp_lemmas_token g_simp_sizeof_tk;

static basic_attribute const & get_simp_sizeof_attribute() {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_simp_sizeof));
}

environment set_simp_sizeof(environment const & env, name const & n) {
    return get_simp_sizeof_attribute().set(env, get_dummy_ios(), n, LEAN_DEFAULT_PRIORITY, true);
}

name mk_has_sizeof_name(name const & ind_name) {
    return ind_name + "has_sizeof_inst";
}

name mk_sizeof_name(name const & ind_name) {
    return ind_name + "sizeof";
}

name mk_sizeof_spec_name(name const & ir_name) {
    return ir_name + "sizeof_spec";
}

class mk_has_sizeof_fn {
    environment    m_env;
    name_generator m_ngen;
    name           m_ind_name;

    expr mk_local_for(expr const & b) {
        return mk_local(m_ngen.next(), binding_name(b), binding_domain(b), binding_info(b));
    }

    expr mk_local_pp(name const & n, expr const & ty) {
        return mk_local(m_ngen.next(), n, ty, binder_info());
    }

    optional<expr> mk_has_sizeof(type_context_old & ctx, expr const & type) {
        level l = get_level(ctx, type);
        expr inst_type = mk_app(mk_constant(get_has_sizeof_name(), {l}), type);
        return ctx.mk_class_instance(inst_type);
    }

    optional<expr> build_has_sizeof_argument_type(type_context_old & ctx, expr const & param) {
        expr ty = ctx.relaxed_whnf(ctx.infer(param));
        buffer<expr> locals;
        while (is_pi(ty)) {
            expr local = mk_local_for(ty);
            locals.push_back(local);
            ty = ctx.relaxed_whnf(instantiate(binding_body(ty), local));
        }
        if (!is_sort(ty))
            return none_expr();
        level l = sort_level(ty);
        return some_expr(Pi(locals, mk_app(mk_constant(get_has_sizeof_name(), {l}),
                                           mk_app(param, locals))));
    }

    optional<expr> is_recursive_arg(type_context_old & ctx, expr const & arg_ty, buffer<expr> & arg_args) {
        expr it = ctx.relaxed_whnf(arg_ty);
        while (is_pi(it)) {
            expr arg_arg = mk_local_for(it);
            arg_args.push_back(arg_arg);
            it = ctx.relaxed_whnf(instantiate(binding_body(it), arg_arg));
        }
        expr fn = get_app_fn(it);
        if (is_constant(fn) && const_name(fn) == m_ind_name)
            return some_expr(it);
        else
            return none_expr();
    }

    void define_instance() {
        type_context_old ctx(m_env);

        auto odecls = inductive::is_inductive_decl(m_env, m_ind_name);
        if (!odecls)
            throw exception(sstream() << "'" << m_ind_name << "' not an inductive datatype\n");

        if (is_inductive_predicate(m_env, m_ind_name) || !can_elim_to_type(m_env, m_ind_name))
            return;

        inductive::inductive_decl decl = *odecls;
        level_param_names lp_names = decl.m_level_params;
        unsigned num_params        = decl.m_num_params;

        expr const & ind_type = decl.m_type;
        buffer<inductive::intro_rule> intro_rules;
        to_buffer(decl.m_intro_rules, intro_rules);

        levels lvls = param_names_to_levels(lp_names);

        name has_sizeof_name = mk_has_sizeof_name(m_ind_name);

        type_context_old::tmp_locals locals(ctx);

        buffer<expr> params;
        buffer<expr> param_insts;
        buffer<expr> indices;
        {
            expr ty = ctx.relaxed_whnf(ind_type);

            // 1. Create locals for the parameters of the inductive type
            for (unsigned param_idx = 0; param_idx < num_params; ++param_idx) {
                expr param = locals.push_local_from_binding(ty);
                params.push_back(param);
                ty = ctx.relaxed_whnf(instantiate(binding_body(ty), param));
            }

            // 2. Add extra [has_sizeof] locals for parameters returning sorts
            for (expr const & param : params) {
                if (auto inst_arg_type = build_has_sizeof_argument_type(ctx, param)) {
                    expr param_inst = locals.push_local(mlocal_pp_name(param).append_after("_inst"), *inst_arg_type, mk_inst_implicit_binder_info());
                    param_insts.push_back(param_inst);
                }
            }

            // 3. Collect indices
            while (is_pi(ty)) {
                expr index = locals.push_local_from_binding(ty);
                indices.push_back(index);
                ty = ctx.relaxed_whnf(instantiate(binding_body(ty), index));
            }
        }

        expr c_ind = mk_app(mk_constant(m_ind_name, lvls), params);

        {
            // Create a new type context so that the [has_sizeof] instances are available for type class resolution
            local_context lctx = ctx.lctx();
            type_context_old ctx(m_env, options(), lctx);

            expr motive;
            {
                expr x = mk_local_pp("x", mk_app(c_ind, indices));
                motive = ctx.mk_lambda(indices, Fun(x, mk_constant(get_nat_name())));
            }

            buffer<expr> minor_premises;
            for (inductive::intro_rule const & ir : intro_rules) {
                expr ir_ty = ctx.relaxed_whnf(inductive::intro_rule_type(ir));
                expr result = mk_nat_one();
                buffer<expr> locals;
                buffer<buffer<expr> > rec_arg_args;

                // Skip the params
                for (unsigned param_idx = 0; param_idx < num_params; ++param_idx) {
                    ir_ty = ctx.relaxed_whnf(instantiate(binding_body(ir_ty), params[param_idx]));
                }

                buffer<expr> ih_locals;
                while (is_pi(ir_ty)) {
                    expr local = mk_local_for(ir_ty);
                    locals.push_back(local);
                    expr arg_ty = binding_domain(ir_ty);

                    buffer<expr> arg_args;
                    if (is_recursive_arg(ctx, arg_ty, arg_args)) {
                        expr ih_local = mk_local_pp("ih", Pi(arg_args, mk_constant(get_nat_name())));
                        ih_locals.push_back(ih_local);
                        if (arg_args.empty()) {
                            /* Remark: recursive arguments of the form (A -> I), where I is the inductive datatype,
                               do not contribute to has_sizeof */
                            result = mk_nat_add(result, ih_local);
                        }
                    } else if (auto inst = mk_has_sizeof(ctx, arg_ty)) {
                        level l = get_level(ctx, arg_ty);
                        result = mk_nat_add(result, mk_app(mk_constant(get_sizeof_name(), {l}), arg_ty, *inst, local));
                    }
                    ir_ty = ctx.relaxed_whnf(instantiate(binding_body(ir_ty), local));
                }
                minor_premises.push_back(Fun(locals, Fun(ih_locals, result)));
            }

            name sizeof_name = mk_sizeof_name(m_ind_name);
            expr sizeof_val =
                mk_app(
                    mk_app(
                        mk_app(
                            mk_app(mk_constant(inductive::get_elim_name(m_ind_name), levels(mk_level_one(), lvls)),
                                   params),
                            motive),
                        minor_premises),
                    indices);
            sizeof_val = ctx.mk_lambda(indices, sizeof_val);
            buffer<expr> used_param_insts;
            for (expr const & param_inst : param_insts) {
                if (find(sizeof_val, [&](expr const & e, unsigned) { return e == param_inst; })) {
                    used_param_insts.push_back(param_inst);
                }
            }
            sizeof_val = ctx.mk_lambda(params, ctx.mk_lambda(used_param_insts, sizeof_val));

            expr sizeof_type = mk_constant(get_nat_name());
            {
                expr x = mk_local_pp("x", mk_app(c_ind, indices));
                sizeof_type = ctx.mk_pi(indices, Pi(x, mk_constant(get_nat_name())));
                sizeof_type = ctx.mk_pi(params, ctx.mk_pi(used_param_insts, sizeof_type));
            }

            lean_trace(name({"constructions", "has_sizeof"}), tout()
                       << "[sizeof]: " << sizeof_name << " : " << sizeof_type << "\n"
                       << sizeof_val << "\n";);

            m_env = module::add(m_env, check(m_env, mk_definition_inferring_trusted(m_env, sizeof_name, lp_names, sizeof_type, sizeof_val, true)));
            m_env = set_reducible(m_env, sizeof_name, reducible_status::Irreducible, true);
            m_env = add_protected(m_env, sizeof_name);

            expr c_sizeof = mk_app(mk_app(mk_constant(sizeof_name, lvls), params), used_param_insts);

            expr has_sizeof_type = ctx.mk_pi(indices,
                                             mk_app(mk_constant(get_has_sizeof_name(), {get_datatype_level(m_env, ind_type)}),
                                                    mk_app(c_ind, indices)));

            expr has_sizeof_val = ctx.mk_lambda(indices,
                                                mk_app(
                                                    mk_app(mk_constant(get_has_sizeof_mk_name(), {get_datatype_level(m_env, ind_type)}),
                                                           mk_app(c_ind, indices)),
                                                    mk_app(c_sizeof, indices)));

            used_param_insts.clear();
            for (expr const & param_inst : param_insts) {
                if (find(has_sizeof_val, [&](expr const & e, unsigned) { return e == param_inst; })) {
                    used_param_insts.push_back(param_inst);
                }
            }

            has_sizeof_type = ctx.mk_pi(params, ctx.mk_pi(used_param_insts, has_sizeof_type));
            has_sizeof_val = ctx.mk_lambda(params, ctx.mk_lambda(used_param_insts, has_sizeof_val));

            lean_trace(name({"constructions", "has_sizeof"}), tout()
                       << "[has_sizeof]: " << has_sizeof_name << " : " << has_sizeof_type << "\n"
                       << has_sizeof_val << "\n";);

            m_env = module::add(m_env, check(m_env, mk_definition_inferring_trusted(m_env, has_sizeof_name, lp_names, has_sizeof_type, has_sizeof_val, true)));
            m_env = add_instance(m_env, has_sizeof_name, LEAN_DEFAULT_PRIORITY, true);
            m_env = add_protected(m_env, has_sizeof_name);

            {
                /* Create new type_context_old with new environment */
                local_context lctx = ctx.lctx();
                type_context_old ctx(m_env, options(), lctx);
                expr c_has_sizeof = mk_app(mk_app(mk_constant(has_sizeof_name, lvls), params), used_param_insts);

                // Defeq simp lemmas
                for (inductive::intro_rule const & ir : intro_rules) {
                    expr ir_ty = ctx.relaxed_whnf(inductive::intro_rule_type(ir));
                    expr c_ir = mk_app(mk_constant(inductive::intro_rule_name(ir), lvls), params);
                    expr rhs = mk_nat_one();
                    buffer<expr> locals;

                    // Skip the params
                    for (unsigned param_idx = 0; param_idx < num_params; ++param_idx) {
                        ir_ty = ctx.relaxed_whnf(instantiate(binding_body(ir_ty), params[param_idx]));
                    }

                    while (is_pi(ir_ty)) {
                        expr local = mk_local_for(ir_ty);
                        locals.push_back(local);
                        expr candidate = mk_app(ctx, get_sizeof_name(), local);
                        type_context_old stctx(m_env, options(), ctx.lctx(), transparency_mode::Semireducible);
                        if (!stctx.is_def_eq(candidate, mk_constant(get_nat_zero_name())))
                            rhs = mk_nat_add(rhs, candidate);
                        ir_ty = ctx.relaxed_whnf(instantiate(binding_body(ir_ty), local));
                    }

                    buffer<expr> args;
                    get_app_args(ir_ty, args);

                    expr lhs = mk_app(mk_app(c_sizeof, indices.size(), args.data() + args.size() - indices.size()), mk_app(c_ir, locals));
                    expr dsimp_rule_type = ctx.mk_pi(params, ctx.mk_pi(used_param_insts, Pi(locals, mk_eq(ctx, lhs, rhs))));
                    expr dsimp_rule_val = ctx.mk_lambda(params, ctx.mk_lambda(used_param_insts, Fun(locals, mk_eq_refl(ctx, lhs))));
                    name dsimp_rule_name = mk_sizeof_spec_name(inductive::intro_rule_name(ir));

                    lean_trace(name({"constructions", "has_sizeof"}), tout() << "eq rule\n"
                               << dsimp_rule_name << " : " << dsimp_rule_type << "\n"
                               << dsimp_rule_val << "\n";);

                    m_env = module::add(m_env, check(m_env, mk_definition_inferring_trusted(m_env, dsimp_rule_name, lp_names, dsimp_rule_type, dsimp_rule_val, true)));
                    m_env = mark_rfl_lemma(m_env, dsimp_rule_name);
                    m_env = add_eqn_lemma(m_env, dsimp_rule_name);
                    m_env = add_protected(m_env, dsimp_rule_name);
                }
            }
        }
    }

public:
    mk_has_sizeof_fn(environment const & env, name const & ind_name):
        m_env(env), m_ngen(mk_constructions_name_generator()), m_ind_name(ind_name) {}

    environment operator()() {
        if (m_env.find(get_has_sizeof_name()))
            define_instance();
        return m_env;
    }
};

name simp_sizeof_attribute_name() {
    return *g_simp_sizeof;
}

simp_lemmas get_sizeof_simp_lemmas(environment const & env) {
    return get_simp_lemmas(env, g_simp_sizeof_tk);
}

void initialize_has_sizeof() {
    g_simp_sizeof    = new name{"_simp", "sizeof"};
    g_simp_sizeof_tk = register_simp_attribute(*g_simp_sizeof, {*g_simp_sizeof}, {});
    register_trace_class(name({"constructions", "has_sizeof"}));
}

void finalize_has_sizeof() {
    delete g_simp_sizeof;
}

environment mk_has_sizeof(environment const & env, name const & ind_name) {
    return mk_has_sizeof_fn(env, ind_name)();
}
}
