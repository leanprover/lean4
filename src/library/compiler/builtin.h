/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Max Wagner
*/
#pragma once
#include <string>
#include "kernel/expr.h"
namespace lean {
bool is_native_constant(environment const & env, name const & c);
bool is_builtin_constant(name const & c);
optional<name> get_native_constant_cname(environment const & env, name const & c);
optional <expr> get_native_constant_ll_type(environment const & env, name const & c);
optional<unsigned> get_native_constant_arity(environment const & env, name const & c);
/* Return true if `c` is a native constant, and store in borrowed_args and
   borrowed_res which arguments/results are marked as borrowed. */
bool get_native_borrowed_info(environment const & env, name const & c, buffer<bool> & borrowed_args, bool & borrowed_res);
/* Return true if `c` is a native constant, and store in used_args a bit mask specifying
which arguments the builtin implementation takes as argument. */
bool get_native_used_args(environment const & env, name const & c, buffer<bool> & used_args);

environment add_native_constant_decl(environment const & env, name const & n, expr const & ll_type, std::string cname,
                                     bool bres, list<bool> const & bargs, list<bool> const & used_args);
void for_each_native_constant(environment const & env, std::function<void(name const & n)> const & f);
void initialize_builtin();
void finalize_builtin();
}
