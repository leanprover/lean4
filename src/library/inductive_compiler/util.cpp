/*
  Copyright (c) 2016 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "util/sexpr/option_declarations.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/util.h"

namespace lean {

implicit_infer_kind get_implicit_infer_kind(name_map<implicit_infer_kind> const & implicit_infer_map, name const & n) {
    if (auto it = implicit_infer_map.find(n))
        return *it;
    else
        return implicit_infer_kind::Implicit;
}

unsigned get_num_indices(environment const & env, expr const & ind) {
    unsigned num_indices = 0;
    type_context_old tctx(env);
    lean_assert(is_local(ind));
    expr ind_type = tctx.relaxed_whnf(mlocal_type(ind));
    type_context_old::tmp_locals locals(tctx);
    while (is_pi(ind_type)) {
        ind_type = instantiate(binding_body(ind_type), locals.push_local_from_binding(ind_type));
        ind_type = tctx.relaxed_whnf(ind_type);
        num_indices++;
    }
    lean_assert(is_sort(ind_type));
    return num_indices;
}

expr get_ind_result_type(type_context_old & tctx, expr const & ind) {
    expr ind_type = tctx.relaxed_whnf(tctx.infer(ind));
    type_context_old::tmp_locals locals(tctx);
    while (is_pi(ind_type)) {
        ind_type = instantiate(binding_body(ind_type), locals.push_local_from_binding(ind_type));
        ind_type = tctx.relaxed_whnf(ind_type);
    }
    lean_assert(is_sort(ind_type));
    return ind_type;
}

void assert_no_locals(name const & n, expr const & e) {
     if (!has_local(e))
        return;
    collected_locals ls;
    collect_locals(e, ls);

    lean_trace(name({"debug", "inductive_compiler"}),
               tout() << "\n\nerror: found locals in '" << n << "'\n" << e << "\n";
               for (expr const & l : ls.get_collected()) {
                   tout() << mlocal_name(l) << "." << mlocal_pp_name(l) << " : " << mlocal_type(l) << "\n";
               });
    lean_assert(false);
}

void assert_def_eq(environment const & DEBUG_CODE(env), expr const & DEBUG_CODE(e1), expr const & DEBUG_CODE(e2)) {
    DEBUG_CODE(type_checker checker(env, true, false /* allow untrusted/meta */););
    try {
        lean_assert(checker.is_def_eq(e1, e2));
    } catch (exception ex) {
        // TODO(dhs): this is only for debugging
        // We prefer to enter GDB than to throw an exception
        lean_assert(false);
        throw ex;
    }
}

void assert_type_correct(environment const & env, expr const & e) {
    type_checker checker(env, true, false /* allow untrusted/meta */);
    try {
        checker.check(e);
    } catch (exception ex) {
        // TODO(dhs): this is only for debugging
        // We prefer to enter GDB than to throw an exception
        lean_assert(false);
        throw ex;
    }
}

expr get_app_params_indices(expr const & e, unsigned num_params, buffer<expr> & params, buffer<expr> & indices) {
    expr fn = get_app_args(e, params);
    lean_assert(params.size() >= num_params);
    for (unsigned i = num_params; i < params.size(); ++i) {
        indices.push_back(params[i]);
    }
    params.shrink(num_params);
    return fn;
}

expr get_app_indices(expr const & e, unsigned num_params, buffer<expr> & indices) {
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    lean_assert(args.size() >= num_params);
    for (unsigned i = num_params; i < args.size(); ++i) {
        indices.push_back(args[i]);
    }
    return fn;
}

void split_params_indices(buffer<expr> const & args, unsigned num_params, buffer<expr> & params, buffer<expr> & indices) {
    for (unsigned i = 0; i < num_params; ++i)
        params.push_back(args[i]);

    for (unsigned i = num_params; i < args.size(); ++i)
        indices.push_back(args[i]);
}
}
