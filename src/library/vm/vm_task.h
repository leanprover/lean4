/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
vm_obj to_obj(task<ts_vm_obj> const & n);
vm_obj to_obj(task<expr> const & n);
bool is_task(vm_obj const & o);
task<expr> to_expr_task(vm_obj const & o);
task<ts_vm_obj> const & to_task(vm_obj const & o);

void initialize_vm_task();
void finalize_vm_task();
}
