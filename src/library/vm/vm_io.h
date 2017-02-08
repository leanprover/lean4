/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
namespace lean {
vm_obj mk_io_result(vm_obj const & r);
void initialize_vm_io();
void finalize_vm_io();
}
