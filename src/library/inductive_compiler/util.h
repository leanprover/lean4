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
expr get_ind_result_type(type_context & tctx, expr const & ind);
void assert_def_eq(environment const & env, expr const & e1, expr const & e2);
void assert_type_correct(environment const & env, expr const & e);
}
