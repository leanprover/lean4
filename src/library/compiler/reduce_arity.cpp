/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/name_map.h"
#include "kernel/free_vars.h"
#include "kernel/for_each_fn.h"
#include "library/trace.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/compiler/procedure.h"
#include "library/compiler/compiler_step_visitor.h"

namespace lean {
static expr reduce_arity_of(expr const & e, unsigned i, std::vector<bool> const & keep_bv) {
    if (i == keep_bv.size())
        return e;
    lean_assert(is_lambda(e));
    expr new_body = reduce_arity_of(binding_body(e), i+1, keep_bv);
    if (keep_bv[i])
        return copy_tag(e, mk_lambda(binding_name(e), binding_domain(e), new_body));
    else
        return lower_free_vars(new_body, 1);
}

/* Auxiliary functor for removing arguments that are not needed in auxiliary function calls */
class remove_args_fn : public compiler_step_visitor {
    /* Mapping from auxiliary function name to bitvector of used arguments */
    name_map<std::vector<bool>> const & m_to_reduce;

    virtual expr visit_macro(expr const & e) override {
        /* This module assumes rec_fn_macros have already been eliminated.
           Remark: the step erase_irrelevant eliminates all occurences. */
        lean_assert(!is_rec_fn_macro(e));
        return compiler_step_visitor::visit_macro(e);
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        if (is_constant(fn)) {
            if (std::vector<bool> const * bv = m_to_reduce.find(const_name(fn))) {
                buffer<expr> args;
                get_app_args(e, args);
                buffer<expr> new_args;
                for (unsigned i = 0; i < args.size(); i++) {
                    /* The case i >= bv->size() can happen when the function is returning a closure.
                       We eta-expand terms, but we may miss cases where the type is opaque (e.g., IO a),
                       or the type is dependent (e.g., T b) where (T is defined as T b := bool.cases_on b nat (nat -> nat)).
                    */
                    if (i >= bv->size() || (*bv)[i])
                        new_args.push_back(visit(args[i]));
                }
                return mk_app(fn, new_args);
            }
        }
        return compiler_step_visitor::visit_app(e);
    }

public:
    remove_args_fn(environment const & env, abstract_context_cache & cache, name_map<std::vector<bool>> const & to_reduce):
        compiler_step_visitor(env, cache), m_to_reduce(to_reduce) {}
};

void reduce_arity(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs) {
    lean_assert(!procs.empty());
    /* Store in to_reduce a bit-vector indicating which arguments are used by each (auxiliary) function. */
    name_map<std::vector<bool>> to_reduce;
    for (unsigned i = 0; i < procs.size() - 1; i++) {
        expr fn = procs[i].m_code;
        std::vector<bool> keep_bv;
        bool reduced = false;
        while (is_lambda(fn)) {
            expr const & body = binding_body(fn);
            if (has_free_var(body,  0)) {
                keep_bv.push_back(true);
            } else {
                keep_bv.push_back(false);
                reduced = true;
            }
            fn = body;
        }
        if (reduced) {
            to_reduce.insert(procs[i].m_name, keep_bv);
        }
    }
    if (to_reduce.empty())
        return;
    /* reduce arity of functions at to_reduce */
    for (unsigned i = 0; i < procs.size() - 1; i++) {
        procedure & d = procs[i];
        if (std::vector<bool> const * bv = to_reduce.find(d.m_name)) {
            d.m_code = reduce_arity_of(d.m_code, 0, *bv);
        }
    }
    /* reduce irrelevant application arguments */
    remove_args_fn remove_args(env, cache, to_reduce);
    for (unsigned i = 0; i < procs.size(); i++) {
        procedure & d = procs[i];
        d.m_code = remove_args(d.m_code);
    }
}
}
