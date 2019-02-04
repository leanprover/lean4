/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
bool is_builtin_constant(name const & c);
optional<name> get_builtin_cname(name const & c);
optional<expr> get_builtin_constant_ll_type(name const & c);
optional<unsigned> get_builtin_constant_arity(name const & c);
/* Return true if `c` is a builtin, and store in borrowed_args and
   borrowed_res which arguments/results are marked as borrowed. */
bool get_builtin_borrowed_info(name const & c, buffer<bool> & borrowed_args, bool & borrowed_res);
/* Return true if `c` is a builtin, and store in used_args a bit mask specifying
   which arguments the builtin implementation takes as argument. */
bool get_builtin_used_args(name const & c, buffer<bool> & used_args);
void initialize_builtin();
void finalize_builtin();
}
