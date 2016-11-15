/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
#include "kernel/expr.h"

namespace lean {
binder_info to_binder_info(vm_obj const & o);
vm_obj to_obj(binder_info const & bi);
macro_definition const & to_macro_definition(vm_obj const & o);
vm_obj to_obj(macro_definition const & d);
bool is_expr(vm_obj const & o);
expr const & to_expr(vm_obj const & o);
vm_obj to_obj(expr const & e);
vm_obj to_obj(optional<expr> const & e);
void initialize_vm_expr();
void finalize_vm_expr();
void initialize_vm_expr_builtin_idxs();
}
