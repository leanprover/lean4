/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "library/vm/vm.h"

namespace lean {
/* Convert exception into vm_exception */
vm_obj to_obj(throwable const & ex);
/* Return fun_idx for vm_exception -> options -> format */
unsigned get_throwable_to_format_fun_idx();
vm_obj mk_vm_exceptional_success(vm_obj const & a);
vm_obj mk_vm_exceptional_exception(throwable const & ex);
void initialize_vm_exceptional();
void finalize_vm_exceptional();
void initialize_vm_exceptional_builtin_idxs();
}
