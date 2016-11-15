/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
#include "kernel/declaration.h"

namespace lean {
bool is_declaration(vm_obj const & o);
declaration const & to_declaration(vm_obj const & o);
vm_obj to_obj(declaration const & n);
void initialize_vm_declaration();
void finalize_vm_declaration();
}
