/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
vm_obj to_obj(task_result<vm_obj> const & n);
vm_obj to_obj(task_result<expr> const & n);
bool is_task(vm_obj const & o);
task_result<expr> to_expr_task(vm_obj const & o);
task_result<vm_obj> & to_task(vm_obj const & o);

void initialize_vm_task();
void finalize_vm_task();
}
