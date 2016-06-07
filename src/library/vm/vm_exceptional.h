/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "library/vm/vm.h"

namespace lean {
vm_obj mk_vm_exceptional_success(vm_obj const & a);
vm_obj mk_vm_exceptional_exception(throwable const & ex);
void initialize_vm_exceptional();
void finalize_vm_exceptional();
void initialize_vm_exceptional_builtin_idxs();
}
