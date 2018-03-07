/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <vector>
#include "library/vm/vm.h"
#include "library/handle.h"

namespace lean {
vm_obj mk_io_result(vm_obj const & r);
vm_obj mk_io_failure(std::string const & s);
/* The io monad produces a result object, or an error.
   If `o` is a result, then we return the result value. */
optional<vm_obj> is_io_result(vm_obj const & o);
/* The io monad produces a result object, or an error.
   If `o` is an error, then we return the io.error value. */
optional<vm_obj> is_io_error(vm_obj const & o);
/* Convert an io.error object into a string */
std::string io_error_to_string(vm_obj const & o);

void set_io_cmdline_args(std::vector<std::string> const & args);

void initialize_vm_io();
void finalize_vm_io();
}
