/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "library/util.h"
#include "library/type_context.h"

namespace lean {

implicit_infer_kind get_implicit_infer_kind(name_map<implicit_infer_kind> const & implicit_infer_map, name const & n);
unsigned get_num_indices(environment const & env, expr const & ind);
expr get_ind_result_type(type_context_old & tctx, expr const & ind);
void assert_def_eq(environment const & env, expr const & e1, expr const & e2);
void assert_type_correct(environment const & env, expr const & e);
void assert_no_locals(name const & n, expr const & e);
expr get_app_params_indices(expr const & e, unsigned num_params, buffer<expr> & params, buffer<expr> & indices);
expr get_app_indices(expr const & e, unsigned num_params, buffer<expr> & indices);
void split_params_indices(buffer<expr> const & args, unsigned num_params, buffer<expr> & params, buffer<expr> & indices);
}
