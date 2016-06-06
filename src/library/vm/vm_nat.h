/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
unsigned to_unsigned(vm_obj const & o);
optional<unsigned> try_to_unsigned(vm_obj const & o);
void initialize_vm_nat();
void finalize_vm_nat();
}
