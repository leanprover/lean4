/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "library/vm/vm_pos_info.h"
#include "library/vm/vm_nat.h"

namespace lean {
pos_info to_pos_info(vm_obj const & o) {
    return {to_unsigned(cfield(o, 0)), to_unsigned(cfield(o, 1))};
}

vm_obj to_obj(pos_info p) {
    return mk_vm_pair(mk_vm_nat(p.first), mk_vm_nat(p.second));
}
}
