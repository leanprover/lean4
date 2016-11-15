/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/vm/vm.h"

namespace lean {
bool is_env(vm_obj const & o);
environment const & to_env(vm_obj const & o);
vm_obj to_obj(environment const & n);
void initialize_vm_environment();
void finalize_vm_environment();
}
