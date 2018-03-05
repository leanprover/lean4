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
#include "library/projection.h"
#include "library/aux_recursors.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/sorry.h"
#include "library/compiler/util.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/eta_expansion.h"

namespace lean {
class eta_expand_fn : public compiler_step_visitor {
    bool m_saw_sorry = false;

    bool is_projection(name const & n) { return ::lean::is_projection(env(), n); }
    bool is_constructor(name const & n) { return static_cast<bool>(is_ginductive_intro_rule(env(), n)); }
    bool is_cases_on(name const & n) { return is_cases_on_recursor(env(), n); }
    bool is_rec(name const & n) { return static_cast<bool>(inductive::is_elim_rule(env(), n)); }
    bool is_no_confusion(name const & n) { return ::lean::is_no_confusion(env(), n);  }
    bool is_quot_mk(name const & n) { return n == get_quot_mk_name(); }
    bool is_quot_lift(name const & n) { return n == get_quot_lift_name(); }
    bool is_subtype_val(name const & n) { return n == get_subtype_val_name(); }
    bool is_pack_unpack(name const & n) { return is_ginductive_pack(env(), n) || is_ginductive_unpack(env(), n); }

    /* Return true if the type of e is of the form
          Pi (a_1 : A_1) ... (a_n : B_n), C
      where C is a Type or a proposition, and n >= 1 */
    bool produces_irrelevant_value(expr const & e) {
        /* TODO(Leo): add "quick check" if this is a performance bottleneck.
           That is, catch easy cases before performing expensive whnf/instantiate. */
        expr type = ctx().relaxed_whnf(ctx().infer(e));
        if (!is_pi(type))
            return false;
        type_context_old::tmp_locals locals(ctx());
        while (is_pi(type)) {
            expr local = locals.push_local_from_binding(type);
            type       = ctx().relaxed_whnf(instantiate(binding_body(type), local));
        }
        return is_sort(type) || ctx().is_prop(type);
    }

    expr eta_expand(expr const & e) {
        return ctx().eta_expand(e);
    }

    /* Returns true if there is a sorry that is not under a lambda. */
    bool has_unguarded_sorry(expr const & e) {
        bool res = false;
        for_each(e, [&] (expr const & e, unsigned off) {
            if (off || is_lambda(e)) return false;
            if (is_sorry(e)) res = true;
            return !res;
        });
        return res;
    }

    expr expand_if_needed(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        name const & fn_name = const_name(fn);

        for (expr & arg : args)
            arg = visit(arg);

        bool revisit = false;

        if (is_rec(fn_name) || is_cases_on(fn_name)) {
            /* Eta-expand minor premises */
            name const & I_name       = fn_name.get_prefix();
            unsigned nparams          = *inductive::get_num_params(env(), I_name);
            unsigned nminors          = *inductive::get_num_minor_premises(env(), I_name);
            unsigned first_minor_idx;
            if (is_rec(fn_name)) {
                first_minor_idx = nparams + 1 /*motive*/;
            } else {
                unsigned nindices = *inductive::get_num_indices(env(), I_name);
                first_minor_idx   = nparams + 1 /*motive*/ + nindices + 1 /*major*/;
            }
            if (first_minor_idx + nminors > args.size()) {
                /* We need to eta-expand the recursor application first */
                revisit = true;
            } else {
                for (unsigned i = first_minor_idx; i < first_minor_idx + nminors; i++)
                    args[i] = eta_expand(args[i]);
            }
        }

        if (is_no_confusion(fn_name)) {
            /*
              Recall that the type of I.no_confusion is of the form:

              Pi (A : Params) (idxs : Indices) (C : Type) (v1 v2 : I A idxs) (h : v1 = v2), I.no_confusion_type C v1 v2

              If v1 and v2 are constructor application (c_1 ...) and (c_2 ...) where c_1 == c_2.,
              then the resulting type (I.no_confusion_type C v1 v2) reduces to ((.. = .. -> ... -> C) -> C)
              Otherwise, it is just C.

              Moreover, the optional extra argument is expected to be eta-expanded at erase_irrelevant.cpp
            */
            name const & I_name       = fn_name.get_prefix();
            unsigned nparams          = *inductive::get_num_params(env(), I_name);
            unsigned nindices         = *inductive::get_num_indices(env(), I_name);
            unsigned pos              = nparams + nindices + 4;
            if (pos >= args.size()) {
                if (is_pi(ctx().relaxed_whnf(ctx().infer(e)))) {
                    /* We need to eta-expand the recursor application first */
                    revisit = true;
                }
            } else {
                args[pos] = eta_expand(args[pos]);
            }
        }

        expr r = mk_app(fn, args);

        if (is_projection(fn_name) || is_constructor(fn_name) ||
            is_rec(fn_name) || is_cases_on(fn_name) ||
            is_no_confusion(fn_name) ||
            is_quot_mk(fn_name) || is_quot_lift(fn_name) ||
            is_subtype_val(fn_name) ||
            is_pack_unpack(fn_name)) {
            if (revisit)
                return visit(eta_expand(r));
            else
                return eta_expand(r);
        } else if (produces_irrelevant_value(r)) {
            /* We don't have bytecode for definitions that produce Type and proofs.
               For example, we don't have code for 'list'.
               Thus, we eta-expand it here (fun x, list x) and rely on erasure step
               to convert it into (fun _, dummy_value).

               Alternative: generate dummy code for everything.
               The bytecode for 'list' would be the constant function that returns the same dummy_value
               (unit in the current implementation). Then, we can remove this check.
            */
            return eta_expand(r);
        } else if (m_saw_sorry && is_pi(ctx().relaxed_whnf(ctx().infer(r))) && has_unguarded_sorry(r)) {
            /* We want to η-expand applications such as `intro ??` into `λ s, intro ?? s`
               to postpone sorry evaluation for as long as possible.

               Later on in lambda-lifting, we need to make sure that we do not reduce
               these expansions again.

               (The has_unguarded_sorry check has linear runtime, so we only do it
               if we saw a sorry at least once.)
            */
            return eta_expand(r);
        } else {
            return r;
        }
    }

    virtual expr visit_constant(expr const & e) override {
        return expand_if_needed(e);
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_sorry(e)) {
            /* We η-expand sorrys to be able to execute tactic scripts with syntax errors.

               For example, when we parse and elaborate `by { simp, simmp }`, we get
               something like `simp >> ??`.
               With η-expansion, the composite tactic becomes `simp >> (λ s, ?? s)`,
               and the execution only fails when we arrive at the syntax error.
            */
            m_saw_sorry = true;
            return eta_expand(e);
        } else {
            return compiler_step_visitor::visit_macro(e);
        }
    }

    virtual expr visit_app(expr const & e) override {
        if (is_constant(get_app_fn(e)))
            return expand_if_needed(e);
        else
            return compiler_step_visitor::visit_app(e);
    }

public:
    eta_expand_fn(environment const & env, abstract_context_cache & cache):
        compiler_step_visitor(env, cache) {}
};

expr eta_expand(environment const & env, abstract_context_cache & cache, expr const & e) {
    return eta_expand_fn(env, cache)(e);
}
}
