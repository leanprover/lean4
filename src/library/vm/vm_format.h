/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/format.h"
#include "library/vm/vm.h"

namespace lean {
format const & to_format(vm_obj const & o);
vm_obj to_obj(format const & fmt);
void initialize_vm_format();
void finalize_vm_format();
}
