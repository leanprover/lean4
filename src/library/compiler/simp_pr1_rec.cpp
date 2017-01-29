/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/compiler/util.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"

namespace lean {
class simp_pr1_rec_fn : public compiler_step_visitor {
    struct failed {};

    struct elim_nested_pr1_fn : public replace_visitor {
        buffer<bool> const & minor_is_rec_arg;
        buffer<expr> const & minor_ctx;

        elim_nested_pr1_fn(buffer<bool> const & b1, buffer<expr> const & b2):
            minor_is_rec_arg(b1), minor_ctx(b2) {
            lean_assert(minor_is_rec_arg.size() == minor_ctx.size());
        }

        bool is_rec_arg(expr const & e) {
            buffer<expr> e_args;
            expr const & fn = get_app_args(e, e_args);
            if (!is_local(fn))
                return false;
            for (unsigned i = 0; i < minor_ctx.size(); i++) {
                if (minor_is_rec_arg[i] && mlocal_name(minor_ctx[i]) == mlocal_name(fn)) {
                    /* make sure arguments contain only valid occurrences */
                    for (expr const & e_arg : e_args)
                        visit(e_arg);
                    return true;
                }
            }
            return false;
        }

        virtual expr visit_app(expr const & e) {
            expr const & f = get_app_fn(e);
            if (is_constant(f) && const_name(f) == get_pprod_fst_name()) {
                buffer<expr> args;
                get_app_args(e, args);
                if (args.size() >= 3 && is_rec_arg(args[2])) {
                    for (unsigned i = 3; i < args.size(); i++)
                        args[i] = visit(args[i]);
                    return copy_tag(e, mk_app(args[2], args.size() - 3, args.data() + 3));
                }
            }
            return replace_visitor::visit_app(e);
        }

        virtual expr visit_local(expr const & e) {
            if (is_rec_arg(e)) {
                throw failed();
            }
            return replace_visitor::visit_local(e);
        }
    };

    optional<expr> simplify(expr const & e) {
        expr const & f = get_app_fn(e);
        if (!is_constant(f) || const_name(f) != get_pprod_fst_name())
            return none_expr();
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() < 3)
            return none_expr();
        for (unsigned i = 3; i < args.size(); i++)
            args[i] = visit(args[i]);
        expr const & rec    = args[2];
        buffer<expr> rec_args;
        expr const & rec_fn = get_app_args(rec, rec_args);
        if (!is_constant(rec_fn))
            return none_expr();
        auto I_name = inductive::is_elim_rule(env(), const_name(rec_fn));
        if (!I_name)
            return none_expr();
        buffer<buffer<bool>> is_rec_arg;
        get_rec_args(env(), *I_name, is_rec_arg);
        unsigned nparams       = *inductive::get_num_params(env(), *I_name);
        unsigned nminors       = *inductive::get_num_minor_premises(env(), *I_name);
        if (rec_args.size() < nparams + 1 /* motive/typeformer */ + nminors)
            return none_expr();
        // Update motive/typeformer
        // Check whether motive is of the form
        //  (lambda ctx, prod c1 c2), and replace it with (lambda ctx, c1)
        unsigned motive_idx = nparams;
        expr typeformer = rec_args[motive_idx];
        buffer<expr> typeformer_ctx;
        /* ignore annotations */
        typeformer = get_nested_annotation_arg(typeformer);
        expr typeformer_body = fun_to_telescope(typeformer, typeformer_ctx, optional<binder_info>());
        /* ignore annotations */
        typeformer_body = get_nested_annotation_arg(typeformer_body);
        buffer<expr> typeformer_body_args;
        expr typeformer_body_fn = get_app_args(typeformer_body, typeformer_body_args);
        if (!is_constant(typeformer_body_fn) ||
            const_name(typeformer_body_fn) != get_pprod_name() ||
            typeformer_body_args.size() != 2) {
            return none_expr();
        }
        typeformer_body = typeformer_body_args[0];
        /* Resultant universe level may have changed. We should recompute it. */
        level new_lvl = sort_level(ctx().whnf(ctx().infer(typeformer_body)));
        /* Update new_rec_fn */
        expr new_rec_fn      = mk_constant(const_name(rec_fn), levels(new_lvl, tail(const_levels(rec_fn))));
        rec_args[motive_idx] = mark_comp_irrelevant(Fun(typeformer_ctx, typeformer_body));

        // Update minor premises
        for (unsigned i = nparams + 1 /* motive */, j = 0; i < nparams + 1 /* motive */ + nminors; i++, j++) {
            buffer<bool> const & minor_is_rec_arg = is_rec_arg[j];
            expr minor = rec_args[i];
            buffer<expr> minor_ctx;
            expr minor_body = fun_to_telescope(minor, minor_ctx, optional<binder_info>());
            if (minor_is_rec_arg.size() != minor_ctx.size()) {
                return none_expr();
            }
            // We have to check:
            //   1- For each local r in the context minor_ctx s.t. r is marked as recursive in minor_is_rec_arg,
            //      its type is of the form (prod A B). The new type will be just A.
            //   2- minor body is of the form (prod.mk A B c1 c2)
            //   3- In c1, all occurrences of recursive arguments r are of the form (prod.fst A B r)

            // Step 1.
            for (unsigned k = 0; k < minor_ctx.size(); k++) {
                if (minor_is_rec_arg[k]) {
                    expr type = ctx().whnf(ctx().infer(minor_ctx[k]));
                    type_context::tmp_locals locals(ctx());
                    while (is_pi(type)) {
                        expr l = locals.push_local(binding_name(type), binding_domain(type), binding_info(type));
                        type = instantiate(binding_body(type), l);
                        type = ctx().whnf(type);
                    }
                    buffer<expr> type_args;
                    expr type_fn = get_app_args(type, type_args);
                    if (!is_constant(type_fn) || const_name(type_fn) != get_pprod_name() || type_args.size() != 2) {
                        return none_expr();
                    }
                    minor_ctx[k] = update_mlocal(minor_ctx[k], locals.mk_pi(type_args[0]));
                }
            }

            // Step 2
            buffer<expr> minor_body_args;
            expr minor_body_fn = get_app_args(minor_body, minor_body_args);
            if (!is_constant(minor_body_fn) ||
                const_name(minor_body_fn) != get_pprod_mk_name() ||
                minor_body_args.size() != 4) {
                return none_expr();
            }
            minor_body = minor_body_args[2];

            // Step 3
            try {
                elim_nested_pr1_fn elim(minor_is_rec_arg, minor_ctx);
                minor_body = elim(minor_body);
            } catch (failed &) {
                return none_expr();
            }
            // Update minor premise
            rec_args[i] = Fun(minor_ctx, minor_body);
        }
        expr new_rec = mk_app(new_rec_fn, rec_args.size(), rec_args.data());
        return some_expr(visit(mk_app(new_rec, args.size() - 3, args.data() + 3)));
    }

    virtual expr visit_app(expr const & e) {
        if (auto r = simplify(e))
            return copy_tag(e, expr(*r));
        else
            return compiler_step_visitor::visit_app(e);
    }

    virtual expr visit_pi(expr const & e) { return e; }

public:
    simp_pr1_rec_fn(environment const & env):compiler_step_visitor(env) {}
};

expr simp_pr1_rec(environment const & env, expr const & e) {
    return simp_pr1_rec_fn(env)(e);
}
}
