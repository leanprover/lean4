/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/format.h"
#include "library/vm/vm.h"

namespace lean {
bool is_format(vm_obj const & o);
format const & to_format(vm_obj const & o);
vm_obj to_obj(format const & fmt);

/* Return an object of type (unit -> format) */
vm_obj mk_vm_format_thunk(std::function<format()> const & fn);

void initialize_vm_format();
void finalize_vm_format();
void initialize_vm_format_builtin_idxs();
}
