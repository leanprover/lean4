/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_set.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
namespace lean {
name_set collect_univ_params(expr const & e, name_set const & ls = name_set());
void collect_locals(expr const & e, expr_struct_set & ls);
level_param_names to_level_param_names(name_set const & ls);
}
