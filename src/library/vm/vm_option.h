/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
inline vm_obj mk_vm_none() { return mk_vm_simple(0); }
inline vm_obj mk_vm_some(vm_obj const & a) { return mk_vm_constructor(1, 1, &a); }
}
