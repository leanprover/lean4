/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "library/type_context.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/app_builder.h"
#include "library/aux_definition.h"
#include "frontends/lean/elaborator.h"
#include "library/replace_visitor_with_tc.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/tactic_evaluator.h"
#include "library/equations_compiler/pack_domain.h"
#include "library/equations_compiler/pack_mutual.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/util.h"

namespace lean {
#define trace_wf(Code) lean_trace(name({"eqn_compiler", "wf_rec"}), type_context_old ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)
#define trace_debug_wf(Code) lean_trace(name({"debug", "eqn_compiler", "wf_rec"}), type_context_old ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)
#define trace_debug_wf_aux(Code) lean_trace(name({"debug", "eqn_compiler", "wf_rec"}), scope_trace_env _scope1(m_env, ctx); Code)

struct wf_rec_fn {
    environment      m_env;
    elaborator &     m_elab;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;

    expr             m_R;
    expr             m_R_wf;

    expr             m_dec_tac;

    wf_rec_fn(environment const & env, elaborator & elab,
              metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_elab(elab), m_mctx(mctx), m_lctx(lctx) {
    }

    type_context_old mk_type_context(local_context const & lctx) {
        return type_context_old(m_env, m_mctx, lctx, m_elab.get_cache(), transparency_mode::Semireducible);
    }

    type_context_old mk_type_context() {
        return mk_type_context(m_lctx);
    }

    options const & get_options() const {
        return m_elab.get_options();
    }

    expr pack_domain(expr const & eqns) {
        type_context_old ctx = mk_type_context();
        expr r = ::lean::pack_domain(ctx, eqns);
        m_env  = ctx.env();
        m_mctx = ctx.mctx();
        return r;
    }

    expr pack_mutual(expr const & eqns) {
        type_context_old ctx = mk_type_context();
        expr r = ::lean::pack_mutual(ctx, eqns);
        m_env  = ctx.env();
        m_mctx = ctx.mctx();
        return r;
    }

    void mk_wf_relation(expr const & eqns, expr const & rel_tac) {
        lean_assert(get_equations_header(eqns).m_num_fns == 1);
        type_context_old ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        name fn_name = head(get_equations_header(eqns).m_fn_names);
        vm_obj vm_fn   = to_obj(ues.get_fn(0));
        vm_obj vm_eqns = to_obj(to_list(ues.get_eqns_of(0)));
        buffer<vm_obj> extra_args;
        extra_args.push_back(vm_fn);
        extra_args.push_back(vm_eqns);
        try {
            expr fn_type          = ctx.relaxed_whnf(ctx.infer(ues.get_fn(0)));
            lean_assert(is_pi(fn_type));
            expr d                = binding_domain(fn_type);
            expr has_well_founded = mk_app(ctx, get_has_well_founded_name(), d);
            tactic_state s        = mk_tactic_state_for(m_env, get_options(), name(fn_name, "_wf_rec_mk_rel_tactic"), m_mctx, m_lctx, has_well_founded);
            vm_obj r = tactic_evaluator(ctx, get_options(), m_ref)(rel_tac, extra_args, s);
            if (auto new_s = tactic::is_success(r)) {
                metavar_context mctx = new_s->mctx();
                bool postpone_push_delayed = true;
                expr val = mctx.instantiate_mvars(new_s->main(), postpone_push_delayed);
                bool mask[2] = {true, true};
                expr args[2] = {d, val};
                m_R    = mk_app(ctx, get_has_well_founded_r_name(), 2, mask, args);
                m_R_wf = mk_app(ctx, get_has_well_founded_wf_name(), 2, mask, args);
                m_env  = new_s->env();
                return;
            }
        } catch (exception & ex) {
            throw nested_exception(some_expr(m_ref),
                                   "failed to create well founded relation using tactic",
                                   ex);
        }
        throw generic_exception(m_ref, "failed to create well founded relation using tactic");
    }

    void init(expr const & eqns, expr const & wf_tacs) {
        expr rel_tac = mk_app(mk_constant(get_well_founded_tactics_rel_tac_name()), wf_tacs);
        mk_wf_relation(eqns, rel_tac);
        m_dec_tac    = mk_app(mk_constant(get_well_founded_tactics_dec_tac_name()), wf_tacs);
    }

    /* Return the type of the functional. */
    expr mk_new_fn_type(type_context_old & ctx, unpack_eqns const & ues) {
        type_context_old::tmp_locals locals(ctx);
        expr fn        = ues.get_fn(0);
        expr fn_type   = ctx.relaxed_whnf(ctx.infer(fn));
        lean_assert(ues.get_arity_of(0) == 1);
        expr x         = locals.push_local("_x", binding_domain(fn_type));
        expr y         = locals.push_local("_y", binding_domain(fn_type));
        expr hlt       = mk_app(m_R, y, x);
        expr Cy        = instantiate(binding_body(fn_type), y);
        expr F_type    = ctx.mk_pi(y, mk_arrow(hlt, Cy));
        expr F         = locals.push_local("_F", F_type);
        expr Cx        = instantiate(binding_body(fn_type), x);
        return ctx.mk_pi(x, ctx.mk_pi(F, Cx));
    }

    struct elim_rec_apps_fn : public replace_visitor_with_tc {
        wf_rec_fn & m_parent;
        name        m_fn_name;
        expr        m_fn;
        expr        m_x;
        expr        m_F;

        elim_rec_apps_fn(wf_rec_fn & parent, type_context_old & ctx, name const & fn_name, expr const & fn, expr const & x, expr const & F):
            replace_visitor_with_tc(ctx), m_parent(parent), m_fn_name(fn_name), m_fn(fn), m_x(x), m_F(F) {}

        virtual expr visit_local(expr const & e) {
            if (mlocal_name(e) == mlocal_name(m_fn)) {
                /* unexpected occurrence of recursive function */
                throw generic_exception(e, "unexpected occurrence of recursive function\n");
            }
            return e;
        }

        /* Prove that y < x */
        expr mk_dec_proof(expr const & y, expr const & ref) {
            expr y_R_x = mk_app(m_parent.m_R, y, m_x);

            metavar_context mctx = m_ctx.mctx();
            tactic_state s = mk_tactic_state_for(m_parent.m_env, m_parent.get_options(),
                                                 name(m_fn_name, "_wf_rec_mk_dec_tactic"), mctx, m_ctx.lctx(), y_R_x);
            try {
                vm_obj r = tactic_evaluator(m_ctx, m_parent.get_options(), ref)(m_parent.m_dec_tac, s);
                if (auto new_s = tactic::is_success(r)) {
                    mctx = new_s->mctx();
                    bool postpone_push_delayed = true;
                    expr r = mctx.instantiate_mvars(new_s->main(), postpone_push_delayed);
                    m_parent.m_env = new_s->env();
                    m_ctx.set_env(new_s->env());
                    m_ctx.set_mctx(mctx);
                    return r;
                }
            } catch (elaborator_exception & ex) {
                bool using_well_founded = is_wf_equations(m_parent.m_ref);
                auto R = m_parent.m_R;
                nested_exception ex2(
                    ex.get_pos(),
                    [=](formatter const & fmt) {
                        format r;
                        formatter _fmt = fmt;
                        if (is_app_of(R, get_has_well_founded_r_name())) {
                            options o = fmt.get_options();
                            o         = o.update_if_undef(get_pp_implicit_name(), true);
                            _fmt      = fmt.update_options(o);
                        }
                        r += format("failed to prove recursive application is decreasing, well founded relation");
                        r += pp_indent_expr(_fmt, R);
                        if (!using_well_founded) {
                            r += line() + format("Possible solutions: ");
                            r += line() + format("  - Use 'using_well_founded' keyword in the end of your definition "
                                                "to specify tactics for synthesizing well founded relations and "
                                                "decreasing proofs.");
                            r += line() + format("  - The default decreasing tactic uses the 'assumption' tactic, "
                                                "thus hints (aka local proofs) can be provided using 'have'-expressions.");
                        }
                        r += line() + format("The nested exception contains the failure state for the decreasing tactic.");
                        return r;
                    },
                    ex);
                if (!m_parent.m_elab.try_report(ex2)) throw ex2;
            }

            return m_parent.m_elab.mk_sorry(y_R_x);
        }

        virtual expr visit_app(expr const & e) {
            expr const & fn = app_fn(e);
            if (is_local(fn) && mlocal_name(fn) == mlocal_name(m_fn)) {
                expr y   = visit(app_arg(e));
                expr hlt = mk_dec_proof(y, e);
                return mk_app(m_F, y, hlt);
            } else {
                return replace_visitor::visit_app(e);
            }
        }
    };

    void update_eqs(type_context_old & ctx, name const & fn_name, unpack_eqns & ues, expr const & fn, expr const & new_fn) {
        buffer<expr> & eqns = ues.get_eqns_of(0);
        buffer<expr> new_eqns;
        for (expr const & eqn : eqns) {
            unpack_eqn ue(ctx, eqn);
            expr lhs = ue.lhs();
            expr rhs = ue.rhs();
            buffer<expr> lhs_args;
            get_app_args(lhs, lhs_args);
            lean_assert(lhs_args.size() == 1);
            expr new_lhs = mk_app(new_fn, lhs_args);
            expr type    = ctx.whnf(ctx.infer(new_lhs));
            lean_assert(is_pi(type));
            ue.lhs()     = new_lhs;
            type_context_old::tmp_locals locals(ctx);
            expr F       = locals.push_local_from_binding(type);
            ue.rhs()     = ctx.mk_lambda(F, elim_rec_apps_fn(*this, ctx, fn_name, fn, lhs_args[0], F)(rhs));
            new_eqns.push_back(ue.repack());
        }
        eqns = new_eqns;
    }

    expr elim_recursion(expr const & eqns) {
        type_context_old ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        lean_assert(ues.get_num_fns() == 1);
        expr fn      = ues.get_fn(0);
        expr fn_type = ctx.infer(fn);
        name fn_name = head(get_equations_header(eqns).m_fn_names);
        expr new_fn_type = mk_new_fn_type(ctx, ues);
        trace_debug_wf(tout() << "\n"; tout() << "new function type: " << new_fn_type << "\n";);
        expr new_fn      = ues.update_fn_type(0, new_fn_type);
        update_eqs(ctx, fn_name, ues, fn, new_fn);
        expr new_eqns    = ues.repack();
        trace_debug_wf(tout() << "after well_founded elim_recursion:\n" << new_eqns << "\n";);
        m_mctx = ctx.mctx();
        return new_eqns;
    }

    expr mk_fix(expr const & aux_fn) {
        type_context_old ctx = mk_type_context();
        type_context_old::tmp_locals locals(ctx);
        buffer<expr> fn_args;
        expr it   = ctx.relaxed_whnf(ctx.infer(aux_fn));
        lean_assert(is_pi(it));
        expr x_ty = binding_domain(it);
        expr x    = locals.push_local("_x", x_ty);
        it        = ctx.relaxed_whnf(instantiate(binding_body(it), x));
        lean_assert(is_pi(it));
        expr Cx   = binding_body(it);
        lean_assert(closed(it));
        expr C    = ctx.mk_lambda(x, Cx);
        level u_1 = get_level(ctx, x_ty);
        level u_2 = get_level(ctx, Cx);
        expr fix  = mk_app({mk_constant(get_well_founded_fix_name(), {u_1, u_2}), x_ty, C, m_R, m_R_wf, aux_fn, x});
        return ctx.mk_lambda(x, fix);
    }

    expr mk_fix_aux_function(equations_header const & header, expr fn) {
        type_context_old ctx = mk_type_context();
        fn = mk_fix(fn);
        expr fn_type = ctx.infer(fn);
        expr r;
        std::tie(m_env, r) = mk_aux_definition(m_env, get_options(), m_mctx, m_lctx, header,
                                               head(header.m_fn_names), head(header.m_fn_actual_names),
                                               fn_type, fn);
        return r;
    }

    struct mk_lemma_rhs_fn : public replace_visitor_with_tc {
        expr m_fn;
        expr m_F;

        mk_lemma_rhs_fn(type_context_old & ctx, expr const & fn, expr const & F):
            replace_visitor_with_tc(ctx), m_fn(fn), m_F(F) {}

        virtual expr visit_local(expr const & e) override {
            if (e == m_F) {
                throw exception("equation compiler failed to generate equational lemmas");
            } else {
                return e;
            }
        }

        virtual expr visit_app(expr const & e) override {
            if (is_app(app_fn(e)) && app_fn(app_fn(e)) == m_F) {
                return mk_app(m_fn, visit(app_arg(app_fn(e))));
            } else {
                return replace_visitor::visit_app(e);
            }
        }
    };

    expr mk_lemma_rhs(type_context_old & ctx, expr const & fn, expr rhs) {
        rhs = ctx.relaxed_whnf(rhs);
        lean_assert(is_lambda(rhs));
        type_context_old::tmp_locals locals(ctx);
        expr F = locals.push_local_from_binding(rhs);
        rhs    = instantiate(binding_body(rhs), F);
        return mk_lemma_rhs_fn(ctx, fn, F)(rhs);
    }

    void mk_lemmas(name const & fn_name, expr const & fn, list<expr> const & lemmas) {
        name const & fn_prv_name = const_name(get_app_fn(fn));
        unsigned eqn_idx     = 1;
        type_context_old ctx     = mk_type_context();
        for (expr type : lemmas) {
            type_context_old::tmp_locals locals(ctx);
            type = ctx.relaxed_whnf(type);
            while (is_pi(type)) {
                expr local = locals.push_local_from_binding(type);
                type = instantiate(binding_body(type), local);
            }
            lean_assert(is_eq(type));
            expr lhs = app_arg(app_fn(type));
            expr rhs = app_arg(type);
            expr new_lhs = mk_app(fn, app_arg(lhs));
            expr new_rhs = mk_lemma_rhs(ctx, fn, rhs);
            trace_debug_wf_aux(tout() << "aux equation [" << eqn_idx << "]:\n" << new_lhs << "\n=\n" << new_rhs << "\n";);
            m_env = mk_equation_lemma(m_env, get_options(), m_mctx, ctx.lctx(), fn_name, fn_prv_name,
                                      eqn_idx, m_header.m_is_private, locals.as_buffer(), new_lhs, new_rhs);
            eqn_idx++;
        }
        m_mctx = ctx.mctx();
    }

    expr_pair mk_sigma(type_context_old & ctx, unsigned i, buffer<expr> const & args) {
        lean_assert(args.size() > 0);
        if (i == args.size() - 1) {
            return mk_pair(args[i], ctx.infer(args[i]));
        } else {
            expr as, as_type;
            std::tie(as, as_type) = mk_sigma(ctx, i+1, args);
            expr a       = args[i];
            lean_assert(is_local(a));
            expr a_type  = ctx.infer(a);
            level a_lvl  = get_level(ctx, a_type);
            level as_lvl = get_level(ctx, as_type);
            as_type     = ctx.mk_lambda(a, as_type);
            expr r_type = mk_app(mk_constant(get_psigma_name(), {a_lvl, as_lvl}), a_type, as_type);
            expr r      = mk_app(mk_constant(get_psigma_mk_name(), {a_lvl, as_lvl}),
                                 a_type, as_type, a, as);
            return mk_pair(r, r_type);
        }
    }

    static optional<expr> unpack_app(expr const & e,
                                     name const & packed_name, unsigned packed_num_params,
                                     unpack_eqns const & ues, buffer<expr> const & result_fns) {
        if (!is_app(e)) return none_expr();
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (!is_constant(fn)) return none_expr();
        if (const_name(fn) != packed_name) return none_expr();
        if (args.size() != packed_num_params + 1) return none_expr();
        expr arg = app_arg(e);
        unsigned num_fns = ues.get_num_fns();
        expr result_fn;
        unsigned fn_idx = 0;
        /* Recall that if we have 4 mutually recursive functions, we encode them as

           f_1 a = _mutual (inl a)
           f_2 b = _mutual (inr (inl b))
           f_3 c = _mutual (inr (inr (inl c)))
           f_4 d = _mutual (inr (inr (inr c)))
         */
        if (num_fns > 1) {
            while (is_app_of(arg, get_psum_inr_name())) {
                fn_idx++;
                arg = app_arg(arg);
            }
            if (is_app_of(arg, get_psum_inl_name())) {
                arg = app_arg(arg);
            }
        }
        result_fn = result_fns[fn_idx];
        unsigned arity = ues.get_arity_of(fn_idx);
        buffer<expr> result_args;
        for (unsigned i = 0; i < arity - 1; i++) {
            lean_assert(is_app_of(arg, get_psigma_mk_name()));
            result_args.push_back(app_arg(app_fn(arg)));
            arg = app_arg(arg);
        }
        result_args.push_back(arg);
        /* Replace parameters and universe levels in result_fn.
           This code is not very robust since it assume the parameter order is the same. */
        expr new_result_fn = mk_app(mk_constant(const_name(get_app_fn(result_fn)), const_levels(fn)),
                                    packed_num_params, args.data());
        return some_expr(mk_app(new_result_fn, result_args.size(), result_args.data()));
    }

    struct unpack_apps_fn : public replace_visitor_with_tc {
        name                 m_packed_name;
        unsigned             m_packed_num_params;
        unpack_eqns const &  m_ues;
        buffer<expr> const & m_result_fns;

        unpack_apps_fn(type_context_old & ctx, name const & packed_name, unsigned packed_num_params,
                       unpack_eqns const & ues, buffer<expr> const & result_fns):
            replace_visitor_with_tc(ctx), m_packed_name(packed_name), m_packed_num_params(packed_num_params),
            m_ues(ues), m_result_fns(result_fns) {
        }

        virtual expr visit_app(expr const & e) override {
            if (auto r = unpack_app(e, m_packed_name, m_packed_num_params, m_ues, m_result_fns)) {
                return visit(*r);
            } else {
                return replace_visitor::visit_app(e);
            }
        }
    };

    eqn_compiler_result unpack(expr const & packed_fn, expr const & eqns_before_pack,
                               list<list<expr>> const & counter_example_args) {
        equations_header const & header = get_equations_header(eqns_before_pack);
        list<name> fn_names     = header.m_fn_names;
        list<name> fn_actual_names = header.m_fn_actual_names;
        type_context_old ctx = mk_type_context();
        buffer<expr> result_fns;
        expr packed_fn_type = ctx.relaxed_whnf(ctx.infer(packed_fn));
        expr packed_domain  = binding_domain(packed_fn_type);
        unpack_eqns ues(ctx, eqns_before_pack);
        unsigned num_fns = ues.get_num_fns();
        for (unsigned fidx = 0; fidx < num_fns; fidx++) {
            unsigned arity = ues.get_arity_of(fidx);
            expr fn_type   = ctx.infer(ues.get_fn(fidx));
            type_context_old::tmp_locals args(ctx);
            expr it        = fn_type;
            for (unsigned i = 0; i < arity; i++) {
                it = ctx.relaxed_whnf(it);
                lean_assert(is_pi(it));
                expr arg = args.push_local_from_binding(it);
                it = instantiate(binding_body(it), arg);
            }
            expr sigma_mk       = mk_sigma(ctx, 0, args.as_buffer()).first;
            expr packed_arg     = mk_mutual_arg(ctx, sigma_mk, fidx, num_fns, packed_domain);
            expr fn_val         = args.mk_lambda(mk_app(packed_fn, packed_arg));
            name fn_name        = head(fn_names);
            name fn_actual_name = head(fn_actual_names);
            fn_names            = tail(fn_names);
            fn_actual_names     = tail(fn_actual_names);
            trace_debug_wf(tout() << fn_name << " := " << fn_val << "\n";);
            expr r;
            std::tie(m_env, r) = mk_aux_definition(m_env, get_options(), m_mctx, m_lctx, header, fn_name, fn_actual_name,
                                                   fn_type, fn_val);
            result_fns.push_back(r);
        }
        ctx.set_env(m_env);
        name const & packed_name   = const_name(get_app_fn(packed_fn));
        unsigned packed_num_params = get_app_num_args(packed_fn);
        /* unpack equations */
        if (m_header.m_aux_lemmas) {
            unsigned i = 1;
            unsigned next_eqn_idx = 1;
            bool has_prev_fn_name = false;
            name prev_fn_name;
            while (true) {
                name packed_eqn_name = mk_equation_name(packed_name, i);
                optional<declaration> packed_eqn_decl = m_env.find(packed_eqn_name);
                if (!packed_eqn_decl) break;
                list<level> packed_eqn_levels = param_names_to_levels(packed_eqn_decl->get_univ_params());
                expr packed_eqn_type = instantiate_type_univ_params(*packed_eqn_decl, packed_eqn_levels);
                type_context_old::tmp_locals args(ctx);
                expr packed_eqn = packed_eqn_type;
                while (true) {
                    packed_eqn = ctx.relaxed_whnf(packed_eqn);
                    if (!is_pi(packed_eqn))
                        break;
                    expr arg   = args.push_local_from_binding(packed_eqn);
                    packed_eqn = instantiate(binding_body(packed_eqn), arg);
                }
                expr lhs, rhs;
                lean_verify(is_eq(packed_eqn, lhs, rhs));
                trace_debug_wf(tout() << "unpacking: " << packed_eqn_name << "\n";
                               tout() << lhs << " = " << rhs << "\n";);
                optional<expr> new_lhs = unpack_app(lhs, packed_name, packed_num_params, ues, result_fns);
                lean_assert(new_lhs);
                expr           new_rhs = unpack_apps_fn(ctx, packed_name, packed_num_params, ues, result_fns)(rhs);
                trace_debug_wf(tout() << "after unpacking\n";
                               tout() << *new_lhs << " = " << new_rhs << "\n";);
                name fn_name   = const_name(get_app_fn(*new_lhs));
                if (!has_prev_fn_name || fn_name != prev_fn_name) {
                    next_eqn_idx = 1;
                } else {
                    next_eqn_idx++;
                }
                prev_fn_name     = fn_name;
                has_prev_fn_name = true;
                expr new_eqn     = mk_eq(ctx, *new_lhs, new_rhs);
                expr new_type    = args.mk_pi(new_eqn);
                expr new_proof   = args.mk_lambda(mk_app(mk_constant(packed_eqn_decl->get_name(), packed_eqn_levels),
                                                       args.size(), args.data()));
                m_env = mk_aux_lemma(m_env, ctx.mctx(), ctx.lctx(),
                                     mk_equation_name(fn_name, next_eqn_idx),
                                     new_type, new_proof).first;
                i++;
            }
        }

        list<expr> counter_examples = map2<expr>(counter_example_args,
            [&] (list<expr> const & es) {
                auto packed_e = mk_app(packed_fn, es);
                auto unpacked_e = unpack_app(packed_e, packed_name, packed_num_params, ues, result_fns);
                return unpacked_e ? *unpacked_e : packed_e;
            });
        return {to_list(result_fns), counter_examples};
    }

    eqn_compiler_result operator()(expr eqns) {
        m_ref    = eqns;
        m_header = get_equations_header(eqns);
        /* Make sure all functions are unary */
        expr before_pack = eqns;
        eqns = pack_domain(eqns);
        trace_debug_wf(tout() << "after pack_domain\n" << eqns << "\n";);

        /* Make sure we have only one function */
        expr before_mutual = eqns;
        equations_header const & header = get_equations_header(eqns);
        if (header.m_num_fns > 1) {
            eqns = pack_mutual(eqns);
        } else {
            equations_header new_header   = header;
            new_header.m_fn_names         = to_list(name(head(header.m_fn_names), "_pack"));
            new_header.m_fn_actual_names  = to_list(name(head(header.m_fn_actual_names), "_pack"));
            eqns                          = update_equations(eqns, new_header);
        }

        /* Retrieve well founded relation */
        expr wf_tacs;
        if (is_wf_equations(eqns)) {
            wf_tacs = equations_wf_tactics(eqns);
        } else {
            wf_tacs = mk_constant(get_well_founded_tactics_default_name());
        }

        init(eqns, wf_tacs);

        /* Eliminate recursion using functional. */
        eqns = elim_recursion(eqns);
        trace_debug_wf(tout() << "after elim_recursion\n" << eqns << "\n";);

        /* Eliminate pattern matching */
        elim_match_result r = elim_match(m_env, m_elab, m_mctx, m_lctx, eqns);
        expr fn = mk_fix_aux_function(get_equations_header(eqns), r.m_fn);

        trace_debug_wf(tout() << "after mk_fix\n" << fn << " :\n  " << mk_type_context().infer(fn) << "\n";);
        if (m_header.m_aux_lemmas) {
            lean_assert(!m_header.m_is_meta);
            equations_header const & header = get_equations_header(eqns);
            name const & fn_name = head(header.m_fn_names);
            mk_lemmas(fn_name, fn, r.m_lemmas);
        }

        return unpack(fn, before_pack, r.m_counter_examples);
    }
};

/** \brief (Try to) eliminate "recursive calls" in the equations \c eqns by using well founded recursion.
    If successful, elim_match is used to compile pattern matching. */
eqn_compiler_result wf_rec(environment & env, elaborator & elab,
                           metavar_context & mctx, local_context const & lctx,
                           expr const & eqns) {
    wf_rec_fn proc(env, elab, mctx, lctx);
    auto r = proc(eqns);
    env    = proc.m_env;
    mctx   = proc.m_mctx;
    return r;
}

bool uses_well_founded_recursion(environment const & env, name const & n) {
    if (!n.is_atomic() && n.is_string() &&
        (strcmp(n.get_string(), "_mutual") == 0 || strcmp(n.get_string(), "_pack") == 0)) {
        return true;
    }
    declaration d = env.get(n);
    expr val = d.get_value();
    while (is_lambda(val))
        val = binding_body(val);
    expr const & fn = get_app_fn(val);
    if (!is_constant(fn))
        return false;
    name const & fn_name = const_name(fn);
    if (!fn_name.is_string() || fn_name.get_string()[0] != '_')
        return false;
    return uses_well_founded_recursion(env, fn_name);
}

void initialize_wf_rec() {
    register_trace_class({"eqn_compiler", "wf_rec"});
    register_trace_class({"debug", "eqn_compiler", "wf_rec"});
}

void finalize_wf_rec() {
}
}
