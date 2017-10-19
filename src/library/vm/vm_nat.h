/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <limits>
#include "library/vm/vm.h"

namespace lean {
unsigned to_unsigned(vm_obj const & o);
optional<unsigned> try_to_unsigned(vm_obj const & o);
unsigned force_to_unsigned(vm_obj const & o, unsigned def = std::numeric_limits<unsigned>::max());
size_t force_to_size_t(vm_obj const & o, size_t def = std::numeric_limits<size_t>::max());
void initialize_vm_nat();
void finalize_vm_nat();
}
