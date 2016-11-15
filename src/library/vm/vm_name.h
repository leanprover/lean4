/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
bool is_name(vm_obj const & o);
name const & to_name(vm_obj const & o);
vm_obj to_obj(name const & n);
void initialize_vm_name();
void finalize_vm_name();
}
