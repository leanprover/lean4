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

template<typename T>
vm_obj to_obj(optional<T> const & o) {
    return o ? mk_vm_some(to_obj(*o)) : mk_vm_none();
}

inline bool is_none(vm_obj const & o) { return is_simple(o); }
inline vm_obj get_some_value(vm_obj const & o) { lean_assert(!is_none(o)); return cfield(o, 0); }
}
