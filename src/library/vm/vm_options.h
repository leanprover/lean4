/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
bool is_options(vm_obj const & o);
options const & to_options(vm_obj const & o);
vm_obj to_obj(options const & n);
void initialize_vm_options();
void finalize_vm_options();
}
