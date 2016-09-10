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
#include "library/attribute_manager.h"
#include "library/inductive_compiler/util.h"

namespace lean {

implicit_infer_kind get_implicit_infer_kind(name_map<implicit_infer_kind> const & implicit_infer_map, name const & n) {
    if (auto it = implicit_infer_map.find(n))
        return *it;
    else
        return implicit_infer_kind::Implicit;
}

expr get_ind_result_type(type_context & tctx, expr const & ind) {
    expr ind_type = tctx.relaxed_whnf(mlocal_type(ind));
    type_context::tmp_locals locals(tctx);
    while (is_pi(ind_type)) {
        ind_type = instantiate(binding_body(ind_type), locals.push_local_from_binding(ind_type));
        ind_type = tctx.relaxed_whnf(ind_type);
    }
    lean_assert(is_sort(ind_type));
    return ind_type;
}

void assert_def_eq(environment const & env, expr const & e1, expr const & e2) {
    type_checker checker(env);
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
    type_checker checker(env);
    try {
        checker.check(e);
    } catch (exception ex) {
        // TODO(dhs): this is only for debugging
        // We prefer to enter GDB than to throw an exception
        lean_assert(false);
        throw ex;
    }
}
}
