/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
/* cmp_result inductive datatype is defined as

      inductive cmp_result :=
      | lt | eq | gt

   The following function converts
     lt -> -1
     eq -> 0
     gt -> 1
*/
inline int cmp_result_to_int(vm_obj const & o) {
    return static_cast<int>(cidx(o)) - 1;
}

/* Convert an integer representing a comparison result into a cmp_result value */
inline vm_obj int_to_cmp_result(int i) {
    if (i < 0) return mk_vm_simple(0);
    else if (i == 0) return mk_vm_simple(1);
    else return mk_vm_simple(2);
}
}
