/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
namespace lean {
bool is_extern_constant(environment const & env, name const & c);
bool is_extern_or_init_constant(environment const & env, name const & c);
optional<expr> get_extern_constant_ll_type(environment const & env, name const & c);
optional<unsigned> get_extern_constant_arity(environment const & env, name const & c);
typedef object_ref extern_attr_data_value;
optional<extern_attr_data_value> get_extern_attr_data(environment const & env, name const & c);
/* Return true if `c` is an extern constant, and store in borrowed_args and
   borrowed_res which arguments/results are marked as borrowed. */
bool get_extern_borrowed_info(environment const & env, name const & c, buffer<bool> & borrowed_args, bool & borrowed_res);
}
