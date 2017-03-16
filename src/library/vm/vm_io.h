/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "library/vm/vm.h"
#include "library/handle.h"

namespace lean {
vm_obj mk_io_result(vm_obj const & r);
vm_obj mk_io_interface();
/* The io monad produces a result object, or an error.
   If `o` is a result, then we return the result value. */
optional<vm_obj> is_io_result(vm_obj const & o);
/* The io monad produces a result object, or an error.
   If `o` is an error, then we return the io.error value. */
optional<vm_obj> is_io_error(vm_obj const & o);
/* Convert an io.error object into a string */
std::string io_error_to_string(vm_obj const & o);

bool is_handle(vm_obj const & o);
handle_ref const & to_handle(vm_obj const & o);
vm_obj to_obj(handle_ref const & h);

void initialize_vm_io();
void finalize_vm_io();
}
