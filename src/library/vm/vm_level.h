/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
#include "kernel/level.h"

namespace lean {
bool is_level(vm_obj const & o);
level const & to_level(vm_obj const & o);
vm_obj to_obj(level const & n);
void initialize_vm_level();
void finalize_vm_level();
}
