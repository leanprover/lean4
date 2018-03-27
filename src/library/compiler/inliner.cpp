/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/normalize.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/compiler/util.h"
#include "library/compiler/compiler_step_visitor.h"

namespace lean {
bool is_inline(environment const & env, name const & n) {
    // declaration is marked with [inline]
    if (has_attribute(env, "inline", n)) {
        return true;
    }
    // decl._main is an auxiliary declaration, check decl instead
    if (n.is_string() && n.get_string()[0] == '_') {
        return is_inline(env, n.get_prefix());
    }
    return false;
}

void initialize_inliner() {
    register_system_attribute(basic_attribute::with_check(
            "inline", "mark definition to always be inlined",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition() || decl.is_theorem())
                    throw exception(
                            "invalid 'inline' use, only definitions can be marked as inline");
            }));
}

void finalize_inliner() {
}

class inline_simple_definitions_fn : public compiler_step_visitor {
    /* Return true iff v is of the form (g y_1 ... y_n) where
       y_i is a constant or a variable.
       Moreover, y_i's variables are pairwise distinct. */
    bool is_simple_application(expr const & v) {
        buffer<expr> ys;
        buffer<bool> bitmap;
        expr const & g = get_app_args(v, ys);
        if (!is_constant(g) && !is_var(g))
            return false;
        for (expr const & y : ys) {
            if (!is_var(y) && !is_constant(y))
                return false;
            if (is_var(y)) {
                unsigned vidx = var_idx(y);
                if (vidx >= bitmap.size())
                    bitmap.resize(vidx+1, false);
                if (bitmap[vidx]) {
                    /* y_i's are not pairwise distinct */
                    return false;
                }
                bitmap[vidx] = true;
            }
        }
        return true;
    }

    expr default_visit_app(expr const & e) {
        expr new_e = compiler_step_visitor::visit_app(e);
        if (new_e != e)
            return visit(new_e);
        else
            return new_e;
    }

    bool is_nonrecursive_recursor(name const & n) {
        if (auto I_name = inductive::is_elim_rule(env(), n)) {
            return !is_recursive_datatype(env(), *I_name);
        }
        return false;
    }

    /* Try to reduce cases_on (and nonrecursive recursor) application
       if major became a constructor */
    expr visit_cases_on_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        for (expr & arg : args)
            arg = visit(arg);
        bool is_cases_on            = is_cases_on_recursor(env(), const_name(fn));
        name const & rec_name       = const_name(fn);
        name const & I_name         = rec_name.get_prefix();
        unsigned nparams            = *inductive::get_num_params(env(), I_name);
        unsigned nindices           = *inductive::get_num_indices(env(), I_name);
        unsigned major_idx;
        if (is_cases_on) {
            major_idx       = nparams + 1 + nindices;
        } else {
            major_idx       = *inductive::get_elim_major_idx(env(), rec_name);
        }
        if (major_idx >= args.size())
            return copy_tag(e, mk_app(fn, args));
        expr major = beta_reduce(args[major_idx]);
        if (is_constructor_app(env(), major)) {
            /* Major premise became a constructor. So, we should reduce. */
            expr new_e = copy_tag(e, mk_app(fn, args));
            if (is_cases_on) {
                /* unfold cases_on */
                if (auto r = unfold_term(env(), new_e))
                    new_e = *r;
                else
                    return new_e;
            }
            /* reduce */
            if (auto r = ctx().norm_ext(new_e))
                return copy_tag(e, visit(beta_reduce(*r)));
        }
        return copy_tag(e, mk_app(fn, args));
    }

    optional<expr> reduce_projection(expr const & e) {
        /* When trying to reduce a projection, we should only unfold reducible constants. */
        type_context_old::transparency_scope _(ctx(), transparency_mode::Instances);
        return ctx().reduce_projection(e);
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return default_visit_app(e);
        name const & n  = const_name(fn);
        if (is_vm_builtin_function(n) || is_pack_unpack(env(), e))
            return default_visit_app(e);
        if (is_cases_on_recursor(env(), n) || is_nonrecursive_recursor(n))
            return visit_cases_on_app(e);
        unsigned nargs  = get_app_num_args(e);
        declaration d   = env().get(n);
        if (!d.is_definition() || d.is_theorem())
            return default_visit_app(e);
        expr v = d.get_value();
        unsigned arity = 0;
        while (is_lambda(v)) {
            arity++;
            v = binding_body(v);
        }

        if (is_inline(env(), n) || (is_simple_application(v) && arity <= nargs)) {
            if (auto r = unfold_term(env(), e))
                return visit(copy_tag(e, expr(*r)));
        }

        if (arity <= nargs) {
            if (auto r = reduce_projection(e)) {
                return visit(*r);
            }
        }

        return default_visit_app(e);
    }

public:
    inline_simple_definitions_fn(environment const & env, abstract_context_cache & cache):
        compiler_step_visitor(env, cache) {}
};

expr inline_simple_definitions(environment const & env, abstract_context_cache & cache, expr const & e) {
    return inline_simple_definitions_fn(env, cache)(e);
}
}
