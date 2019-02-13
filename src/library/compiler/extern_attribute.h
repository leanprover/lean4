/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
bool is_extern_constant(environment const & env, name const & c);
optional<expr> get_extern_constant_ll_type(environment const & env, name const & c);
optional<unsigned> get_extern_constant_arity(environment const & env, name const & c);
/* Return true if `c` is an extern constant, and store in borrowed_args and
   borrowed_res which arguments/results are marked as borrowed. */
bool get_extern_borrowed_info(environment const & env, name const & c, buffer<bool> & borrowed_args, bool & borrowed_res);

bool emit_extern_call_core(std::ostream & out, environment const & env, name const & backend, name const & fn, string_refs const & attrs);
void emit_extern_call(std::ostream & out, environment const & env, name const & backend, name const & fn, string_refs const & attrs);

optional<std::string> get_extern_name_for(environment const & env, name const & backend, name const & fn);

/* We say a Lean function marked as `[extern "<c_fn_nane>"]` is for all backends, and it is implemented using `extern "C"`.
   Thus, there is no name mangling. */
bool is_extern_c(environment const & env, name const & fn);

void initialize_extern_attribute();
void finalize_extern_attribute();
}
